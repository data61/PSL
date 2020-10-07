(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Inv4 imports DiskPaxos_Inv2  begin

subsection \<open>Invariant 4\<close>

text \<open>
  This invariant expresses relations among $mbal$ and $bal$ values of a 
  processor and of its disk blocks. 
  $HInv4a$ asserts that, when $p$ is not recovering from a failure, its 
  $mbal$ value is at least as large as the $bal$ field of any of its blocks,
  and at least as large as the $mbal$ field of its block on some disk in
  any majority set. 
  $HInv4b$ conjunct asserts that, in phase 1, its $mbal$ value is actually 
  greater than the $bal$ field of any of its blocks. 
  $HInv4c$ asserts that, in phase 2, its $bal$ value is the $mbal$ field 
  of all its blocks on some majority set of disks. 
  $HInv4d$ asserts that the $bal$ field of any of its blocks is at most as 
  large as the $mbal$ field of all its disk blocks on some majority set of disks.
\<close>

definition MajoritySet :: "Disk set set"
  where "MajoritySet = {D. IsMajority(D) }"

definition HInv4a1 :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv4a1 s p = (\<forall>bk \<in> blocksOf s p. bal bk  \<le> mbal (dblock s p))"

definition HInv4a2 :: "state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "HInv4a2 s p = (\<forall>D \<in> MajoritySet.(\<exists>d \<in> D.  mbal(disk s d p) \<le> mbal(dblock s p)
                                           \<and> bal(disk s d p) \<le> bal(dblock s p)))"

definition HInv4a :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv4a s p = (phase s p \<noteq> 0 \<longrightarrow> HInv4a1 s p \<and> HInv4a2 s p)"

definition HInv4b :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv4b s p = (phase s p = 1 \<longrightarrow> (\<forall>bk \<in> blocksOf s p. bal bk < mbal(dblock s p)))"

definition HInv4c :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv4c s p = (phase s p \<in> {2,3} \<longrightarrow> (\<exists>D\<in>MajoritySet. \<forall>d\<in>D. mbal(disk s d p) = bal (dblock s p)))" 

definition HInv4d :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv4d s p = (\<forall>bk \<in> blocksOf s p. \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p))"

definition HInv4 :: "state \<Rightarrow> bool"
  where "HInv4 s = (\<forall>p. HInv4a s p \<and> HInv4b s p \<and> HInv4c s p \<and> HInv4d s p)"

text \<open>The initial state implies Invariant 4.\<close>

theorem HInit_HInv4: "HInit s \<Longrightarrow> HInv4 s"
  using Disk_isMajority
  by(auto simp add: HInit_def Init_def HInv4_def HInv4a_def HInv4a1_def 
                    HInv4a2_def HInv4b_def HInv4c_def HInv4d_def 
                    MajoritySet_def blocksOf_def InitDB_def rdBy_def)

text \<open>To prove that the actions preserve $HInv4$,
        we do it for one conjunct at a time.

  For each action $action s s' q$ and conjunct $x\in{a,b,c,d}$ of $HInv4x s' p$, 
  we prove two lemmas. 
The first lemma $action$-$HInv4x$-$p$ proves the case of $p=q$, while 
lemma $action$-$HInv4x$-$q$ proves the other case.
\<close>

subsubsection \<open>Proofs of Invariant 4a\<close>

lemma HStartBallot_HInv4a1:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4a1 s p"
  and inv2a: "Inv2a_inner s' p"
  shows "HInv4a1 s' p"
proof(auto simp add: HInv4a1_def)
  fix bk
  assume "bk \<in> blocksOf s' p"
  with HStartBallot_blocksOf[OF act] 
  have "bk \<in> {dblock s' p} \<union> blocksOf s p"
    by blast
  thus "bal bk \<le> mbal (dblock s' p)"
  proof
    assume "bk \<in> {dblock s' p}"
    with inv2a
    show ?thesis
      by(auto simp add: Inv2a_innermost_def Inv2a_inner_def blocksOf_def)
  next
    assume "bk \<in> blocksOf s p"
    with inv act
    show ?thesis
      by(auto simp add: StartBallot_def HInv4a1_def)
  qed
qed

lemma HStartBallot_HInv4a2:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4a2 s p"
  shows "HInv4a2 s' p"
proof(auto simp add: HInv4a2_def)
  fix D
  assume Dmaj: "D \<in> MajoritySet"
  from inv Dmaj
  have "\<exists>d\<in>D.   mbal (disk s d p) \<le> mbal (dblock s p) 
              \<and> bal (disk s d p) \<le> bal (dblock s p)"
    by(auto simp add: HInv4a2_def)
  then obtain d 
    where "  d\<in>D 
           \<and> mbal (disk s d p) \<le> mbal (dblock s p) 
           \<and> bal (disk s d p) \<le> bal (dblock s p)" 
    by auto
  with act
  have "  d\<in>D 
        \<and> mbal (disk s' d p) \<le> mbal (dblock s' p) 
        \<and> bal (disk s' d p) \<le> bal (dblock s' p)"
    by(auto simp add: StartBallot_def)
  with Dmaj
  show "\<exists>d\<in>D.   mbal (disk s' d p) \<le> mbal (dblock s' p) 
              \<and> bal (disk s' d p) \<le> bal (dblock s' p)"
    by auto
qed

lemma HStartBallot_HInv4a_p:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4a s p"
  and inv2a: "Inv2a_inner s' p"
  shows "HInv4a s' p"
using act inv inv2a
proof -
  from act
  have phase: "0 < phase s p"
    by(auto simp add: StartBallot_def)
  from act inv inv2a
  show ?thesis
    by(auto simp del: HStartBallot_def simp  add: HInv4a_def phase
               elim: HStartBallot_HInv4a1 HStartBallot_HInv4a2)
qed

lemma HStartBallot_HInv4a_q:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4a s q"
  and pnq: "p\<noteq>q"
  shows "HInv4a s' q"
proof -
  from act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: StartBallot_def InitializePhase_def 
                      blocksOf_def rdBy_def)
  with act inv pnq
  show ?thesis
    by(auto simp add: StartBallot_def HInv4a_def 
                      HInv4a1_def HInv4a2_def)
qed

theorem HStartBallot_HInv4a:
  assumes act: "HStartBallot s s' p"
  and  inv: "HInv4a s q"
  and inv2a: "Inv2a s'"
  shows "HInv4a s' q"
proof(cases "p=q")
  case True
  from inv2a
  have "Inv2a_inner s' p"
    by(auto simp add: Inv2a_def)
  with act inv True
  show ?thesis
    by(blast dest: HStartBallot_HInv4a_p)
next
  case False
  with act inv
  show ?thesis
    by(blast dest: HStartBallot_HInv4a_q)
qed

lemma Phase1or2Write_HInv4a1:
  "\<lbrakk> Phase1or2Write s s' p d; HInv4a1 s q \<rbrakk> \<Longrightarrow> HInv4a1 s' q"
  by(auto simp add: Phase1or2Write_def HInv4a1_def 
                    blocksOf_def rdBy_def)

lemma Phase1or2Write_HInv4a2:
  "\<lbrakk> Phase1or2Write s s' p d; HInv4a2 s q \<rbrakk> \<Longrightarrow> HInv4a2 s' q"
  by(auto simp add: Phase1or2Write_def HInv4a2_def)

theorem HPhase1or2Write_HInv4a:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv4a s q"
  shows "HInv4a s' q"
proof -
  from act
  have phase': "phase s = phase s'"
    by(simp add: Phase1or2Write_def)
  show ?thesis
  proof(cases "phase s q = 0")
  case True
  with phase' act
  show ?thesis
    by(auto simp add: HInv4a_def)
next
  case False
  with phase' act inv
  show ?thesis
    by(auto simp add: HInv4a_def 
                dest: Phase1or2Write_HInv4a1 Phase1or2Write_HInv4a2)
  qed
qed

lemma HPhase1or2ReadThen_HInv4a1_p:
  assumes act: "HPhase1or2ReadThen s s' p d q" 
  and     inv: "HInv4a1 s p"
  shows "HInv4a1 s' p"
proof(auto simp: HInv4a1_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  with HPhase1or2ReadThen_blocksOf[OF act]
  have "bk \<in> blocksOf s p" by auto
  with inv act
  show "bal bk \<le> mbal (dblock s' p)"
    by(auto simp add: HInv4a1_def Phase1or2ReadThen_def)
qed

lemma HPhase1or2ReadThen_HInv4a2:
  "\<lbrakk> HPhase1or2ReadThen s s' p d r; HInv4a2 s q \<rbrakk> \<Longrightarrow> HInv4a2 s' q"
  by(auto simp add: Phase1or2ReadThen_def HInv4a2_def)

lemma HPhase1or2ReadThen_HInv4a_p:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv4a s p"
  and inv2b: "Inv2b s"
  shows "HInv4a s' p"
proof -
  from act inv2b
  have "phase s p \<in> {1,2}"
    by(auto simp add: Phase1or2ReadThen_def Inv2b_def Inv2b_inner_def)
  with act inv
  show ?thesis
    by(auto simp del: HPhase1or2ReadThen_def simp add: HInv4a_def
          elim: HPhase1or2ReadThen_HInv4a1_p HPhase1or2ReadThen_HInv4a2)
qed

lemma HPhase1or2ReadThen_HInv4a_q:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv4a s q"
  and pnq: "p\<noteq>q"
  shows "HInv4a s' q"
proof -
  from act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: Phase1or2ReadThen_def InitializePhase_def 
                      blocksOf_def rdBy_def)
  with act inv pnq
  show ?thesis
    by(auto simp add: Phase1or2ReadThen_def HInv4a_def 
                      HInv4a1_def HInv4a2_def)
qed

theorem HPhase1or2ReadThen_HInv4a:
  "\<lbrakk> HPhase1or2ReadThen s s' p d r; HInv4a s q; Inv2b s \<rbrakk> \<Longrightarrow> HInv4a s' q"
  by(blast dest: HPhase1or2ReadThen_HInv4a_p HPhase1or2ReadThen_HInv4a_q)

theorem HPhase1or2ReadElse_HInv4a:
  assumes act: "HPhase1or2ReadElse s s' p d r" 
  and inv: "HInv4a s q" and inv2a: "Inv2a s'"
  shows "HInv4a s' q"
proof -
  from act  have "HStartBallot s s' p"
    by(simp add: Phase1or2ReadElse_def)
  with inv inv2a show ?thesis
    by(blast dest: dest: HStartBallot_HInv4a )
qed

lemma HEndPhase1_HInv4a1:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4a1 s p"
  shows "HInv4a1 s' p"
proof(auto simp add: HInv4a1_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from bk HEndPhase1_blocksOf[OF act] 
  have "bk \<in> {dblock s' p} \<union> blocksOf s p"
    by blast 
  with act inv
  show "bal bk \<le> mbal (dblock s' p)"
    by(auto simp add: HInv4a_def HInv4a1_def EndPhase1_def)
qed

lemma HEndPhase1_HInv4a2:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4a2 s p"
  and inv2a: "Inv2a s"
  shows "HInv4a2 s' p"
proof(auto simp add: HInv4a2_def)
  fix D
  assume Dmaj: "D \<in> MajoritySet"
  from inv Dmaj
  have "\<exists>d\<in>D.   mbal (disk s d p) \<le> mbal (dblock s p) 
              \<and> bal (disk s d p) \<le> bal (dblock s p)"
    by(auto simp add: HInv4a2_def)
  then obtain d 
    where d_cond: "  d\<in>D 
                   \<and> mbal (disk s d p) \<le> mbal (dblock s p) 
                   \<and> bal (disk s d p) \<le> bal (dblock s p)" 
    by auto
  have "disk s d p \<in> blocksOf s p"
    by(auto simp add: blocksOf_def)
  with inv2a
  have "bal(disk s d p) \<le> mbal (disk s d p)"
    by(auto simp add: Inv2a_def Inv2a_inner_def Inv2a_innermost_def)
  with act d_cond
  have "  d\<in>D 
        \<and> mbal (disk s' d p) \<le> mbal (dblock s' p) 
        \<and> bal (disk s' d p) \<le> bal (dblock s' p)"
    by(auto simp add: EndPhase1_def)
  with Dmaj
  show "\<exists>d\<in>D.   mbal (disk s' d p) \<le> mbal (dblock s' p) 
              \<and> bal (disk s' d p) \<le> bal (dblock s' p)"
    by auto
qed

lemma HEndPhase1_HInv4a_p:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4a s p"
  and inv2a: "Inv2a s"
  shows "HInv4a s' p"
proof -
  from act
  have phase: "0 < phase s p"
    by(auto simp add: EndPhase1_def)
  with act inv inv2a
  show ?thesis
    by(auto simp del: HEndPhase1_def simp  add: HInv4a_def 
               elim: HEndPhase1_HInv4a1 HEndPhase1_HInv4a2)
qed

lemma HEndPhase1_HInv4a_q:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4a s q"
  and pnq: "p\<noteq>q"
  shows "HInv4a s' q"
proof -
  from act pnq
  have "dblock s' q = dblock s q \<and> disk s' = disk s"
    by(auto simp add: EndPhase1_def)
  moreover
  from act pnq
  have "\<forall>p d. rdBy s' q p d \<subseteq> rdBy s q p d"
    by(auto simp add: EndPhase1_def InitializePhase_def rdBy_def)
  hence "(UN p d. rdBy s' q p d) \<subseteq> (UN p d. rdBy s q p d)"
    by(auto, blast)
  ultimately
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: blocksOf_def, blast)
  with act inv pnq
  show ?thesis
    by(auto simp add: EndPhase1_def HInv4a_def HInv4a1_def HInv4a2_def)
qed

theorem HEndPhase1_HInv4a:
  "\<lbrakk> HEndPhase1 s s' p; HInv4a s q;  Inv2a s \<rbrakk> \<Longrightarrow> HInv4a s' q"
  by(blast dest: HEndPhase1_HInv4a_p HEndPhase1_HInv4a_q)
 
theorem HFail_HInv4a:
  "\<lbrakk> HFail s s' p; HInv4a s q \<rbrakk> \<Longrightarrow> HInv4a s' q"
  by(auto simp add: Fail_def HInv4a_def HInv4a1_def 
                    HInv4a2_def InitializePhase_def 
                    blocksOf_def rdBy_def)

theorem HPhase0Read_HInv4a:
  "\<lbrakk> HPhase0Read s s' p d; HInv4a s q \<rbrakk> \<Longrightarrow> HInv4a s' q"
  by(auto simp add: Phase0Read_def HInv4a_def HInv4a1_def 
                    HInv4a2_def InitializePhase_def 
                    blocksOf_def rdBy_def)

theorem HEndPhase2_HInv4a:
  "\<lbrakk> HEndPhase2 s s' p; HInv4a s q \<rbrakk> \<Longrightarrow> HInv4a s' q"
  by(auto simp add: EndPhase2_def HInv4a_def HInv4a1_def HInv4a2_def 
                    InitializePhase_def blocksOf_def rdBy_def)

lemma allSet: 
  assumes aPQ: "\<forall>a. \<forall>r \<in> P a. Q r" and  rb: "rb \<in> P d"
  shows "Q rb"
proof - 
  from aPQ have "\<forall>r \<in> P d. Q r" by auto
  with rb
  show ?thesis by auto
qed

lemma EndPhase0_44:
  assumes act: "EndPhase0 s s' p"
  and bk: "bk \<in> blocksOf s p"
  and inv4d: "HInv4d s p"
  and inv2c: "Inv2c_inner s p"
  shows "\<exists>d. \<exists>rb \<in> blocksRead s p d. bal bk \<le> mbal(block rb)"
proof -
  from bk inv4d
  have "\<exists>D1 \<in> MajoritySet.\<forall>d \<in> D1. bal bk \<le> mbal(disk s d p)"  \<comment> \<open>4.2\<close>
    by(auto simp add: HInv4d_def)
  with majorities_intersect
  have p43: "\<forall>D\<in>MajoritySet. \<exists>d\<in>D. bal bk \<le> mbal(disk s d p)"
    by(simp add: MajoritySet_def, blast)
  from act
  have "phase s p = 0" by(simp add: EndPhase0_def)
  with inv2c
  have "\<forall>d. \<forall>rb \<in> blocksRead s p d. block rb = disk s d p" \<comment> \<open>5.1\<close>
    by(simp add: Inv2c_inner_def)
  hence "\<forall>d. hasRead s p d p  
              \<longrightarrow> (\<exists>rb\<in>blocksRead s p d. block rb = disk s d p)" \<comment> \<open>5.2\<close>
    (is "\<forall>d. ?H d \<longrightarrow> ?P d")
    by(auto simp add: hasRead_def)
  with act
  have p53: "\<exists>D \<in> MajoritySet. \<forall>d\<in>D. ?P d"
    by(auto simp add: MajoritySet_def EndPhase0_def)
  show ?thesis
  proof -
    from p43 p53
    have "\<exists>D\<in> MajoritySet.   (\<exists>d\<in>D. bal bk \<le> mbal(disk s d p)) 
                           \<and> (\<forall>d\<in>D. ?P d)"
      by auto
    thus ?thesis
      by force
  qed
qed

lemma HEndPhase0_HInv4a1_p:
  assumes act: "HEndPhase0 s s' p"
  and   inv2a': "Inv2a s'"
  and   inv2c: "Inv2c_inner s p"
  and   inv4d: "HInv4d s p"
  shows "HInv4a1 s' p"
proof(auto simp add: HInv4a1_def)
  fix bk
  assume "bk \<in> blocksOf s' p"
  with HEndPhase0_blocksOf[OF act]
  have "bk \<in> {dblock s' p} \<union> blocksOf s p" by auto
  thus "bal bk \<le> mbal (dblock s' p)"
  proof
    assume bk: "bk \<in> {dblock s' p}"
    with inv2a'
    have "Inv2a_innermost s' p bk"
      by(auto simp add: Inv2a_def Inv2a_inner_def blocksOf_def)
    with bk show ?thesis
      by(auto simp add: Inv2a_innermost_def)
  next
    assume bk: "bk \<in> blocksOf s p"
    from act
    have f1: "\<forall>r \<in> allBlocksRead s p. mbal r < mbal (dblock s' p)"
      by(auto simp add: EndPhase0_def)
    with act inv4d inv2c bk
    have "\<exists>d. \<exists>rb \<in> blocksRead s p d. bal bk \<le> mbal(block rb)"
      by(auto dest: EndPhase0_44)
    with f1
    show ?thesis
      by(auto simp add: EndPhase0_def allBlocksRead_def
                        allRdBlks_def dest: allSet)
  qed
qed

lemma hasRead_allBlks: 
  assumes inv2c: "Inv2c_inner s p"
  and     phase: "phase s p = 0"
  shows "(\<forall>d\<in>{d. hasRead s p d p}. disk s d p \<in> allBlocksRead s p)" 
proof
  fix d
  assume d: "d\<in>{d. hasRead s p d p}" (is "d\<in> ?D")
  hence br_ne: "blocksRead s p d\<noteq>{}"
    by (auto simp add: hasRead_def)
  from inv2c phase
  have "\<forall>br \<in> blocksRead s p d. block br = disk s d p"
    by(auto simp add: Inv2c_inner_def)
  with br_ne
  have "disk s d p \<in> block ` blocksRead s p d" 
    by force
  thus "disk s d p \<in> allBlocksRead s p"
    by(auto simp add: allBlocksRead_def allRdBlks_def)
qed


lemma HEndPhase0_41:
  assumes act: "HEndPhase0 s s' p"
  and    inv1:  "Inv1 s"
  and   inv2c: "Inv2c_inner s p" 
  shows "\<exists>D\<in>MajoritySet. \<forall>d\<in>D.   mbal(disk s d p) \<le> mbal(dblock s' p) 
                               \<and> bal(disk s d p) \<le> bal(dblock s' p)"
proof -
  from act HEndPhase0_some[OF act inv1]
  have p51: "\<forall>br\<in>allBlocksRead s p.   mbal br < mbal(dblock s' p) 
                                    \<and> bal br \<le> bal(dblock s' p)"     
    and a: "IsMajority({d. hasRead s p d p})" 
    and phase: "phase s p = 0"
    by(auto simp add: EndPhase0_def)+
  from inv2c phase
  have "(\<forall>d\<in>{d. hasRead s p d p}. disk s d p \<in> allBlocksRead s p)"
    by(auto dest: hasRead_allBlks)
  with p51
  have "(\<forall>d\<in>{d. hasRead s p d p}.   mbal(disk s d p) \<le> mbal(dblock s' p) 
                                  \<and> bal(disk s d p) \<le> bal(dblock s' p))"
    by force
  with a show ?thesis
    by(auto simp add: MajoritySet_def)
qed
  
lemma Majority_exQ: 
  assumes asm1: "\<exists>D \<in> MajoritySet. \<forall>d\<in>D. P d"
  shows "\<forall>D\<in>MajoritySet.\<exists>d\<in>D. P d"
using asm1
proof(auto simp add: MajoritySet_def)
  fix D1 D2
  assume D1: "IsMajority D1" and D2: "IsMajority D2"
     and Px: "\<forall>x\<in>D1. P x"
  from D1 D2 majorities_intersect
  have "\<exists>d\<in>D1. d\<in>D2" by auto
  with Px
  show "\<exists>x\<in>D2. P x"
    by auto
qed

lemma HEndPhase0_HInv4a2_p:
  assumes act: "HEndPhase0 s s' p"
  and    inv1:  "Inv1 s"
  and   inv2c: "Inv2c_inner s p"
  shows "HInv4a2 s' p"
proof(simp add: HInv4a2_def)
  from act
  have disk': "disk s' = disk s"
    by(simp add: EndPhase0_def)
  from act inv1 inv2c
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D.   mbal(disk s d p) \<le> mbal(dblock s' p) 
                              \<and> bal(disk s d p) \<le> bal(dblock s' p)"
    by(blast dest: HEndPhase0_41)
  from Majority_exQ[OF this]
  have  "\<forall>D\<in>MajoritySet. \<exists>d\<in>D.   mbal(disk s d p) \<le> mbal(dblock s' p) 
                               \<and> bal(disk s d p) \<le> bal(dblock s' p)" 
    (is "?P (disk s)") .
  from ssubst[OF disk', of ?P, OF this]
  show "\<forall>D\<in>MajoritySet. \<exists>d\<in>D.  mbal (disk s' d p) \<le> mbal (dblock s' p) 
                              \<and> bal (disk s' d p) \<le> bal (dblock s' p)" .
qed
      
lemma HEndPhase0_HInv4a_p:
  assumes act: "HEndPhase0 s s' p"
  and   inv2a: "Inv2a s"
  and   inv2: "Inv2c s"
  and   inv4d: "HInv4d s p"
  and   inv1: "Inv1 s"
  and inv: "HInv4a s p"
  shows "HInv4a s' p"
proof -
  from inv2
  have inv2c: "Inv2c_inner s p"
    by(auto simp add: Inv2c_def)
  with inv1 inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HEndPhase0_Inv2a)
  from act
  have "phase s' p = 1"
    by(auto simp add: EndPhase0_def)
  with act inv inv2c inv4d inv2a' inv1
  show ?thesis
    by(auto simp  add: HInv4a_def simp del: HEndPhase0_def
          elim: HEndPhase0_HInv4a1_p HEndPhase0_HInv4a2_p)
qed

lemma HEndPhase0_HInv4a_q:
  assumes act: "HEndPhase0 s s' p"
  and inv: "HInv4a s q"
  and pnq: "p\<noteq>q"
  shows "HInv4a s' q"
proof -
  from act pnq
  have "dblock s' q = dblock s q \<and> disk s' = disk s"
    by(auto simp add: EndPhase0_def)
  moreover
  from act pnq
  have "\<forall>p d. rdBy s' q p d \<subseteq> rdBy s q p d"
    by(auto simp add: EndPhase0_def InitializePhase_def rdBy_def)
  hence "(UN p d. rdBy s' q p d) \<subseteq> (UN p d. rdBy s q p d)"
    by(auto, blast)
  ultimately
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: blocksOf_def, blast)
  with act inv pnq
  show ?thesis
    by(auto simp add: EndPhase0_def HInv4a_def HInv4a1_def HInv4a2_def)
qed

theorem HEndPhase0_HInv4a:
  "\<lbrakk> HEndPhase0 s s' p; HInv4a s q; HInv4d s p;
     Inv2a s;  Inv1 s;   Inv2a s; Inv2c s\<rbrakk> 
  \<Longrightarrow> HInv4a s' q"
  by(blast dest: HEndPhase0_HInv4a_p HEndPhase0_HInv4a_q)

subsubsection \<open>Proofs of Invariant 4b\<close>

lemma blocksRead_allBlocksRead: 
  "rb \<in> blocksRead s p d \<Longrightarrow> block rb \<in> allBlocksRead s p"
 by(auto simp add: allBlocksRead_def allRdBlks_def)

lemma HEndPhase0_dblock_mbal:
  "\<lbrakk> HEndPhase0 s  s' p \<rbrakk> 
     \<Longrightarrow> \<forall>br\<in>allBlocksRead s p. mbal br < mbal(dblock s' p)"
  by(auto simp add: EndPhase0_def)


lemma HEndPhase0_HInv4b_p_dblock:
  assumes act: "HEndPhase0 s  s' p"
  and inv1:  "Inv1 s" 
  and inv2a: "Inv2a s"
  and inv2c: "Inv2c_inner s p"
  shows "bal(dblock s' p) < mbal(dblock s' p)"
proof -
  from act have "phase s p = 0" by(auto simp add: EndPhase0_def)
  with inv2c
  have "\<forall>d.\<forall>br\<in>blocksRead s p d. proc br = p \<and> block br = disk s d p"
    by(auto simp add: Inv2c_inner_def)
  hence allBlks_in_blocksOf: "allBlocksRead s p \<subseteq> blocksOf s p"
    by(auto simp add: allBlocksRead_def allRdBlks_def blocksOf_def)
  from act HEndPhase0_some[OF act inv1]
  have p53: "\<exists>br\<in>allBlocksRead s p. bal(dblock s' p)=bal br"
    by(auto simp add: EndPhase0_def)
  from inv2a
  have i2: "\<forall>p. \<forall>bk\<in>blocksOf s p. bal bk \<le> mbal bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def Inv2a_innermost_def)
  with allBlks_in_blocksOf
  have "\<forall>bk\<in>allBlocksRead s p. bal bk \<le> mbal bk"
    by auto
  with p53
  have "\<exists>br\<in>allBlocksRead s p. bal(dblock s' p)\<le> mbal br"
    by force
  with HEndPhase0_dblock_mbal[OF act]
  show ?thesis
    by auto
qed

lemma HEndPhase0_HInv4b_p_blocksOf:
  assumes act: "HEndPhase0 s  s' p"
  and inv4d: "HInv4d s p"
  and inv2c: "Inv2c_inner s p"
  and bk: "bk \<in> blocksOf s p"
  shows "bal bk < mbal(dblock s' p)"
proof -
  from inv4d  majorities_intersect bk
  have p43: "\<forall>D\<in>MajoritySet.\<exists>d\<in>D. bal bk \<le> mbal(disk s d p)"
    by(auto simp add: HInv4d_def MajoritySet_def Majority_exQ)
  have "\<exists>br \<in> allBlocksRead s p. bal bk \<le> mbal br" 
  proof -
    from act
    have maj: "IsMajority({d. hasRead s p d p})" (is "IsMajority(?D)")
     and phase: "phase s p = 0"
      by(simp add: EndPhase0_def)+ 
    have br_ne: "\<forall>d\<in>?D. blocksRead s p d \<noteq> {}"
      by(auto simp add: hasRead_def)
    from phase inv2c
    have "\<forall>d\<in>?D.\<forall>br\<in>blocksRead s p d. block br = disk s d p"
      by(auto simp add: Inv2c_inner_def)
    with br_ne
    have "\<forall>d\<in>?D. \<exists>br\<in> allBlocksRead s p. br = disk s d p"
      by(blast dest: blocksRead_allBlocksRead)
    with p43 maj
    show ?thesis
      by(auto simp add: MajoritySet_def)
  qed
  with HEndPhase0_dblock_mbal[OF act]
  show ?thesis
    by auto
qed

lemma HEndPhase0_HInv4b_p:
  assumes act: "HEndPhase0 s  s' p"
  and inv4d: "HInv4d s p"
  and inv1:  "Inv1 s" 
  and inv2a: "Inv2a s"
  and inv2c: "Inv2c_inner s p"
  shows "HInv4b s' p"
proof(clarsimp simp add: HInv4b_def)
  from act        
  have  phase: "phase s p = 0" 
    by(auto simp add: EndPhase0_def)
  fix bk    
  assume bk: "bk\<in> blocksOf s' p"
  with HEndPhase0_blocksOf[OF act]
  have "bk\<in>{dblock s' p} \<or> bk\<in>blocksOf s p"
    by blast
  thus "bal bk < mbal (dblock s' p)"
  proof
    assume bk: "bk\<in>{dblock s' p}"
    with act inv1 inv2a inv2c
    show ?thesis
      by(auto simp del: HEndPhase0_def 
                  dest: HEndPhase0_HInv4b_p_dblock )
  next
    assume bk: "bk \<in> blocksOf s p"
    with act inv2c inv4d
    show ?thesis
      by(blast dest: HEndPhase0_HInv4b_p_blocksOf)
  qed
qed

lemma HEndPhase0_HInv4b_q:
  assumes act: "HEndPhase0 s  s' p"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: EndPhase0_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: EndPhase0_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  with inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HEndPhase0_HInv4b:
  assumes act: "HEndPhase0 s  s' p"
  and inv: "HInv4b s q"
  and inv4d: "HInv4d s p"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a s" 
  and inv2c: "Inv2c_inner s p"
  shows "HInv4b s' q"
proof(cases "p=q")
  case True
  with HEndPhase0_HInv4b_p[OF act inv4d inv1 inv2a inv2c]
  show ?thesis by simp
next
  case False
  from HEndPhase0_HInv4b_q[OF act False inv]
  show ?thesis .
qed

lemma HStartBallot_HInv4b_p:
  assumes act: "HStartBallot s  s' p"
  and inv2a: "Inv2a_innermost s p (dblock s p)"
  and inv4b: "HInv4b s p"
  and inv4a: "HInv4a s p"
  shows "HInv4b s' p"
proof(clarsimp simp add: HInv4b_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have phase': "phase s' p = 1"
    and phase: "phase s p \<in> {1,2}"
    by(auto simp add: StartBallot_def)
  from act
  have p42: "  mbal (dblock s p)< mbal (dblock s' p)
        \<and> bal(dblock s p) = bal(dblock s' p)"
    by(auto simp add: StartBallot_def)
  from HStartBallot_blocksOf[OF act] bk
  have "bk \<in> {dblock s' p} \<union> blocksOf s p"
    by blast
  thus "bal bk < mbal (dblock s' p)"
  proof
    assume bk: "bk \<in> {dblock s' p}"
    from inv2a
    have "bal (dblock s p) \<le> mbal (dblock s p)"
      by(auto simp add: Inv2a_innermost_def)
    with p42 bk
    show ?thesis by auto
  next
    assume bk: "bk \<in> blocksOf s p"
    from phase inv4a
    have p41: "HInv4a1 s p"
      by(auto simp add: HInv4a_def)
    with p42 bk
    show ?thesis
      by(auto simp add: HInv4a1_def)
  qed
qed
    
lemma HStartBallot_HInv4b_q:
  assumes act: "HStartBallot s  s' p"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: StartBallot_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: StartBallot_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  with inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HStartBallot_HInv4b:
  assumes act: "HStartBallot s  s' p"
  and inv2a: "Inv2a s"
  and inv4b: "HInv4b s q"
  and inv4a: "HInv4a s p"
  shows "HInv4b s' q"
using act inv2a inv4b inv4a
proof (cases "p=q")
  case True
  from inv2a
  have "Inv2a_innermost s p (dblock s p)"
    by(auto simp add: Inv2a_def Inv2a_inner_def blocksOf_def) 
  with act True inv4b inv4a
  show ?thesis
    by(blast dest: HStartBallot_HInv4b_p)
next
  case False
  with act inv4b
  show ?thesis
    by(blast dest: HStartBallot_HInv4b_q)
qed
   
theorem HPhase1or2Write_HInv4b:
  "\<lbrakk> HPhase1or2Write s s' p d; HInv4b s q \<rbrakk> \<Longrightarrow> HInv4b s' q"
  by(auto simp add: Phase1or2Write_def HInv4b_def 
                    blocksOf_def rdBy_def)

lemma HPhase1or2ReadThen_HInv4b_p:
  assumes act: "HPhase1or2ReadThen s s' p d q"
  and inv: "HInv4b s p"
  shows "HInv4b s' p"
proof -
  from HPhase1or2ReadThen_blocksOf[OF act] inv act
  show ?thesis
    by(auto simp add: HInv4b_def Phase1or2ReadThen_def)
qed

lemma HPhase1or2ReadThen_HInv4b_q:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv4b s q"
  and pnq: "p\<noteq>q"
  shows "HInv4b s' q"
  using assms HPhase1or2ReadThen_blocksOf[OF act]
  by(auto simp add: Phase1or2ReadThen_def HInv4b_def)

theorem HPhase1or2ReadThen_HInv4b:
  "\<lbrakk> HPhase1or2ReadThen s s' p d q; HInv4b s r\<rbrakk> \<Longrightarrow> HInv4b s' r"
  by(blast dest: HPhase1or2ReadThen_HInv4b_p 
                 HPhase1or2ReadThen_HInv4b_q)

theorem HPhase1or2ReadElse_HInv4b:
  "\<lbrakk> HPhase1or2ReadElse s s' p d q; HInv4b s r;
     Inv2a s; HInv4a s p \<rbrakk>
  \<Longrightarrow> HInv4b s' r"
using HStartBallot_HInv4b
 by(auto simp add: Phase1or2ReadElse_def)

lemma HEndPhase1_HInv4b_p:
  "HEndPhase1 s s' p \<Longrightarrow> HInv4b s' p"
  by(auto simp add: EndPhase1_def HInv4b_def)

lemma HEndPhase1_HInv4b_q:
  assumes act: "HEndPhase1 s  s' p"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: EndPhase1_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: EndPhase1_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  with inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HEndPhase1_HInv4b:
  assumes act: "HEndPhase1 s  s' p"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof(cases "p=q")
  case True
  with HEndPhase1_HInv4b_p[OF act]
  show ?thesis by simp
next
  case False
  from HEndPhase1_HInv4b_q[OF act False inv]
  show ?thesis .
qed

lemma HEndPhase2_HInv4b_p:
  "HEndPhase2 s s' p \<Longrightarrow> HInv4b s' p"
  by(auto simp add: EndPhase2_def HInv4b_def)

lemma HEndPhase2_HInv4b_q:
  assumes act: "HEndPhase2 s  s' p"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: EndPhase2_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: EndPhase2_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  with inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HEndPhase2_HInv4b:
  assumes act: "HEndPhase2 s  s' p"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof(cases "p=q")
  case True
  with HEndPhase2_HInv4b_p[OF act]
  show ?thesis by simp
next
  case False
  from HEndPhase2_HInv4b_q[OF act False inv]
  show ?thesis .
qed

lemma HFail_HInv4b_p:
  "HFail s s' p \<Longrightarrow> HInv4b s' p"
  by(auto simp add: Fail_def HInv4b_def)

lemma HFail_HInv4b_q:
  assumes act: "HFail s  s' p"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: Fail_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: Fail_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  with inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HFail_HInv4b:
  assumes act: "HFail s  s' p"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof(cases "p=q")
  case True
  with HFail_HInv4b_p[OF act]
  show ?thesis by simp
next
  case False
  from HFail_HInv4b_q[OF act False inv]
  show ?thesis .
qed

lemma HPhase0Read_HInv4b_p:
  "HPhase0Read s s' p d \<Longrightarrow> HInv4b s' p"
  by(auto simp add: Phase0Read_def HInv4b_def)

lemma HPhase0Read_HInv4b_q:
  assumes act: "HPhase0Read s  s' p d"
  and pnq: "p\<noteq>q"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof -
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
   and phase': "phase s' q =phase s q"
    by(auto simp add: Phase0Read_def)
  from HPhase0Read_blocksOf[OF act] inv phase' dblock'
  show ?thesis
    by(auto simp add: HInv4b_def)
qed

theorem HPhase0Read_HInv4b:
  assumes act: "HPhase0Read s  s' p d"
  and inv: "HInv4b s q"
  shows "HInv4b s' q"
proof(cases "p=q")
  case True
  with HPhase0Read_HInv4b_p[OF act]
  show ?thesis by simp
next
  case False
  from HPhase0Read_HInv4b_q[OF act False inv]
  show ?thesis .
qed

subsubsection \<open>Proofs of Invariant 4c\<close>

lemma  HStartBallot_HInv4c_p:
  "\<lbrakk> HStartBallot s s' p; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: StartBallot_def HInv4c_def)

lemma  HStartBallot_HInv4c_q:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: StartBallot_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HStartBallot_HInv4c:
  "\<lbrakk> HStartBallot s s' p; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HStartBallot_HInv4c_p HStartBallot_HInv4c_q)

lemma  HPhase1or2Write_HInv4c_p:
  assumes act: "HPhase1or2Write s s' p d" 
      and inv: "HInv4c s p" 
    and inv2c: "Inv2c s"
  shows "HInv4c s' p"
proof(cases "phase s' p = 2")
  assume phase': "phase s' p = 2"
  show ?thesis
  proof(auto simp add: HInv4c_def phase' MajoritySet_def)
    from act phase'
    have bal: "bal(dblock s' p)=bal(dblock s p)"
      and phase: "phase s p = 2"
      by(auto simp add: Phase1or2Write_def)
    from phase' inv2c act
    have "mbal(disk s' d p)=bal(dblock s p)"
      by(auto simp add: Phase1or2Write_def Inv2c_def Inv2c_inner_def)
    with bal
    have "bal(dblock s' p) = mbal(disk s' d p)"
      by auto
    with inv phase act
    show "\<exists>D.    IsMajority D 
              \<and> (\<forall>d\<in>D. mbal (disk s' d p) = bal (dblock s' p))"
      by(auto simp add: HInv4c_def Phase1or2Write_def MajoritySet_def)
  qed
next
  case False
  with act
  show ?thesis 
    by(auto simp add: HInv4c_def Phase1or2Write_def) 
qed

lemma  HPhase1or2Write_HInv4c_q:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
    and disk: "\<forall>d. disk s' d q  = disk s d q"
    by(auto simp add: Phase1or2Write_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HPhase1or2Write_HInv4c:
  "\<lbrakk> HPhase1or2Write s s' p d; HInv4c s q; Inv2c s \<rbrakk>
             \<Longrightarrow> HInv4c s' q"
  by(blast dest: HPhase1or2Write_HInv4c_p
                 HPhase1or2Write_HInv4c_q)

lemma  HPhase1or2ReadThen_HInv4c_p:
  "\<lbrakk> HPhase1or2ReadThen s s' p d q; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: Phase1or2ReadThen_def HInv4c_def)

lemma  HPhase1or2ReadThen_HInv4c_q:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: Phase1or2ReadThen_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HPhase1or2ReadThen_HInv4c:
  "\<lbrakk> HPhase1or2ReadThen s s' p d r; HInv4c s q\<rbrakk>
          \<Longrightarrow> HInv4c s' q"
  by(blast dest: HPhase1or2ReadThen_HInv4c_p
                 HPhase1or2ReadThen_HInv4c_q)

theorem HPhase1or2ReadElse_HInv4c:
  "\<lbrakk> HPhase1or2ReadElse s s' p d r; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
using HStartBallot_HInv4c
  by(auto simp add: Phase1or2ReadElse_def)

lemma  HEndPhase1_HInv4c_p:
  assumes act: "HEndPhase1 s s' p"
  and inv2b: "Inv2b s"
  shows "HInv4c s' p"
proof -
  from act
  have maj: "   IsMajority {d. d\<in> disksWritten s p 
             \<and> (\<forall>q\<in>(UNIV- {p}). hasRead s p d q)}" 
    (is  "IsMajority ?M")
    by(simp add: EndPhase1_def)
  from inv2b
  have "\<forall>d\<in>?M. disk s d p = dblock s p"
    by(auto simp add: Inv2b_def Inv2b_inner_def)
  with act maj
  show ?thesis
    by(auto simp add: HInv4c_def EndPhase1_def MajoritySet_def)
qed

lemma  HEndPhase1_HInv4c_q:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: EndPhase1_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HEndPhase1_HInv4c:
  "\<lbrakk> HEndPhase1 s s' p; HInv4c s q; Inv2b s\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HEndPhase1_HInv4c_p HEndPhase1_HInv4c_q)

lemma  HEndPhase2_HInv4c_p:
  "\<lbrakk> HEndPhase2 s s' p; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: EndPhase2_def HInv4c_def)

lemma  HEndPhase2_HInv4c_q:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: EndPhase2_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HEndPhase2_HInv4c:
  "\<lbrakk> HEndPhase2 s s' p; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HEndPhase2_HInv4c_p HEndPhase2_HInv4c_q)

lemma  HFail_HInv4c_p:
  "\<lbrakk> HFail s s' p; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: Fail_def HInv4c_def)

lemma  HFail_HInv4c_q:
  assumes act: "HFail s s' p"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: Fail_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HFail_HInv4c:
  "\<lbrakk> HFail s s' p; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HFail_HInv4c_p HFail_HInv4c_q)

lemma  HPhase0Read_HInv4c_p:
  "\<lbrakk> HPhase0Read s s' p d; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: Phase0Read_def HInv4c_def)

lemma  HPhase0Read_HInv4c_q:
  assumes act: "HPhase0Read s s' p d"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: Phase0Read_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HPhase0Read_HInv4c:
  "\<lbrakk> HPhase0Read s s' p d; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HPhase0Read_HInv4c_p HPhase0Read_HInv4c_q)

lemma  HEndPhase0_HInv4c_p:
  "\<lbrakk> HEndPhase0 s s' p; HInv4c s p\<rbrakk> \<Longrightarrow> HInv4c s' p"
  by(auto simp add: EndPhase0_def HInv4c_def)

lemma  HEndPhase0_HInv4c_q:
  assumes act: "HEndPhase0 s s' p"
  and inv: "HInv4c s q"
  and pnq: "p\<noteq>q"
  shows "HInv4c s' q"
proof -
  from act pnq
  have phase: "phase s' q = phase s q"
   and dblock: "dblock s q = dblock s' q"
   and disk: "disk s' = disk s"
    by(auto simp add: EndPhase0_def)
  with inv
  show ?thesis
    by(auto simp add: HInv4c_def)
qed
 
theorem HEndPhase0_HInv4c:
  "\<lbrakk> HEndPhase0 s s' p; HInv4c s q\<rbrakk> \<Longrightarrow> HInv4c s' q"
  by(blast dest: HEndPhase0_HInv4c_p HEndPhase0_HInv4c_q)

subsubsection \<open>Proofs of Invariant 4d\<close>

lemma  HStartBallot_HInv4d_p:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv4d s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have bal': "bal (dblock s' p) = bal (dblock s p)" 
    by(auto simp add: StartBallot_def)
  from subsetD[OF HStartBallot_blocksOf[OF act] bk]
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p)"
  proof
    assume bk: "bk \<in> blocksOf s p"
    with inv
    show ?thesis
      by(auto simp add: HInv4d_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    with bal' inv
    show ?thesis
      by(auto simp add: HInv4d_def blocksOf_def)
  qed
  with act
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: StartBallot_def)
qed

lemma HStartBallot_HInv4d_q:
  assumes act: "HStartBallot s  s' p"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
    by(auto simp add: StartBallot_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: StartBallot_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q. 
           \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HStartBallot_HInv4d:
  "\<lbrakk> HStartBallot s s' p; HInv4d s q\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HStartBallot_HInv4d_p HStartBallot_HInv4d_q)

lemma  HPhase1or2Write_HInv4d_p:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv4d s p"
  and inv4a: "HInv4a s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have ddisk: "\<forall>dd. disk s' dd p = (if d = dd 
                                       then dblock s p 
                                       else disk s dd p)" 
    and phase: "phase s p \<noteq> 0"
    by(auto simp add: Phase1or2Write_def)
  from inv subsetD[OF HPhase1or2Write_blocksOf[OF act] bk]
  have asm3: "\<exists>D\<in>MajoritySet. \<forall>dd\<in>D. bal bk \<le> mbal (disk s dd p)"
    by(auto simp add: HInv4d_def)
  from phase inv4a subsetD[OF HPhase1or2Write_blocksOf[OF act] bk] ddisk
  have p41: "bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: HInv4a_def HInv4a1_def)
  with ddisk asm3
  show "\<exists>D\<in>MajoritySet. \<forall>dd\<in>D. bal bk \<le> mbal (disk s' dd p)"
    by(auto simp add: MajoritySet_def split: if_split_asm)
qed

lemma HPhase1or2Write_HInv4d_q:
  assumes act: "HPhase1or2Write s  s' p d"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "\<forall>d. disk s' d q =disk s  d q" 
    by(auto simp add: Phase1or2Write_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: Phase1or2Write_def 
                      InitializePhase_def allRdBlks_def)
  with act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: Phase1or2Write_def allRdBlks_def
                      blocksOf_def rdBy_def)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q. 
            \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HPhase1or2Write_HInv4d:
  "\<lbrakk> HPhase1or2Write s s' p d; HInv4d s q; HInv4a s p\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HPhase1or2Write_HInv4d_p HPhase1or2Write_HInv4d_q)

lemma  HPhase1or2ReadThen_HInv4d_p:
  assumes act: "HPhase1or2ReadThen s s' p d q"
  and inv: "HInv4d s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have bal': "bal (dblock s' p) = bal (dblock s p)" 
    by(auto simp add: Phase1or2ReadThen_def)
  from subsetD[OF HPhase1or2ReadThen_blocksOf[OF act] bk] inv
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p)"
    by(auto simp add: HInv4d_def)
  with act
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: Phase1or2ReadThen_def)
qed

lemma HPhase1or2ReadThen_HInv4d_q:
  assumes act: "HPhase1or2ReadThen s  s' p d r"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
    by(auto simp add: Phase1or2ReadThen_def)
  from act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: Phase1or2ReadThen_def allRdBlks_def
                      blocksOf_def rdBy_def)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q. 
             \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HPhase1or2ReadThen_HInv4d:
  "\<lbrakk> HPhase1or2ReadThen s s' p d r; HInv4d s q\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HPhase1or2ReadThen_HInv4d_p
                 HPhase1or2ReadThen_HInv4d_q)

theorem HPhase1or2ReadElse_HInv4d:
  "\<lbrakk> HPhase1or2ReadElse s s' p d r; HInv4d s q\<rbrakk> \<Longrightarrow> HInv4d s' q"
using HStartBallot_HInv4d
  by(auto simp add: Phase1or2ReadElse_def)

lemma  HEndPhase1_HInv4d_p:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv4d s p"
  and inv2b: "Inv2b s"
  and inv4c: "HInv4c s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from HEndPhase1_HInv4c[OF act inv4c inv2b]
  have "HInv4c s' p" .
  with act
  have p31: "\<exists>D\<in>MajoritySet. 
               \<forall>d\<in>D. mbal (disk s' d p) = bal(dblock s' p)"
    and disk': "disk s' = disk s"
    by(auto simp add: EndPhase1_def HInv4c_def)
  from subsetD[OF HEndPhase1_blocksOf[OF act] bk]
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
  proof
    assume bk: "bk \<in> blocksOf s p"
    with inv disk'
    show ?thesis
      by(auto simp add: HInv4d_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    with p31
    show ?thesis
      by force
  qed
qed

lemma HEndPhase1_HInv4d_q:
  assumes act: "HEndPhase1 s  s' p"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
    by(auto simp add: EndPhase1_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: EndPhase1_def InitializePhase_def
                      allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q. 
           \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HEndPhase1_HInv4d:
  "\<lbrakk> HEndPhase1 s s' p; HInv4d s q; Inv2b s; HInv4c s p\<rbrakk>
         \<Longrightarrow> HInv4d s' q"
  by(blast dest: HEndPhase1_HInv4d_p HEndPhase1_HInv4d_q)

lemma  HEndPhase2_HInv4d_p:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv4d s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have bal': "bal (dblock s' p) = bal (dblock s p)" 
    by(auto simp add: EndPhase2_def)
  from subsetD[OF HEndPhase2_blocksOf[OF act] bk] inv
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p)"
    by(auto simp add: HInv4d_def)
  with act
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: EndPhase2_def)
qed

lemma HEndPhase2_HInv4d_q:
  assumes act: "HEndPhase2 s  s' p"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
    by(auto simp add: EndPhase2_def)
  from act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: EndPhase2_def InitializePhase_def
                      allRdBlks_def blocksOf_def rdBy_def)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q.
           \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HEndPhase2_HInv4d:
  "\<lbrakk> HEndPhase2 s s' p; HInv4d s q\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HEndPhase2_HInv4d_p HEndPhase2_HInv4d_q)

lemma  HFail_HInv4d_p:
  assumes act: "HFail s s' p"
  and inv: "HInv4d s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have disk': "disk s' = disk s"
    by(auto simp add: Fail_def)
  from subsetD[OF HFail_blocksOf[OF act] bk]
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
  proof
    assume bk: "bk \<in> blocksOf s p"
    with inv disk'
    show ?thesis
      by(auto simp add: HInv4d_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    with act
    have "bal bk = 0"
      by(auto simp add: Fail_def InitDB_def)
    with Disk_isMajority
    show ?thesis
      by(auto simp add: MajoritySet_def)
  qed
qed

lemma HFail_HInv4d_q:
  assumes act: "HFail s  s' p"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
   and dblock': "dblock s' q=dblock s q"
    by(auto simp add: Fail_def)
  from act pnq
  have blocksRead': "\<forall>q. allRdBlks s' q \<subseteq> allRdBlks s q" 
    by(auto simp add: Fail_def InitializePhase_def allRdBlks_def)
  with disk' dblock'
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: allRdBlks_def blocksOf_def rdBy_def, blast)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q.
          \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HFail_HInv4d:
  "\<lbrakk> HFail s s' p; HInv4d s q \<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HFail_HInv4d_p HFail_HInv4d_q)

lemma  HPhase0Read_HInv4d_p:
  assumes act: "HPhase0Read s s' p d"
  and inv: "HInv4d s p"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from act
  have bal': "bal (dblock s' p) = bal (dblock s p)" 
    by(auto simp add: Phase0Read_def)
  from subsetD[OF HPhase0Read_blocksOf[OF act] bk] inv
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p)"
    by(auto simp add: HInv4d_def)
  with act
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: Phase0Read_def)
qed

lemma HPhase0Read_HInv4d_q:
  assumes act: "HPhase0Read s  s' p d"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
  from act pnq
  have disk': "disk s'=disk s" 
    by(auto simp add: Phase0Read_def)
  from act pnq
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: Phase0Read_def allRdBlks_def
                      blocksOf_def rdBy_def)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q.
           \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with disk'
  show ?thesis
  by(auto simp add: HInv4d_def)
qed

theorem HPhase0Read_HInv4d:
  "\<lbrakk> HPhase0Read s s' p d; HInv4d s q\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HPhase0Read_HInv4d_p HPhase0Read_HInv4d_q)

lemma HEndPhase0_blocksOf2:
  assumes act: "HEndPhase0 s s' p"
  and inv2c: "Inv2c_inner s p"
  shows "allBlocksRead s p \<subseteq> blocksOf s p"
proof -
  from act inv2c
  have "\<forall>d.\<forall>br \<in> blocksRead s p d.   proc br =p 
                                    \<and> block br = disk s d p"
    by(auto simp add: EndPhase0_def Inv2c_inner_def)
  thus ?thesis 
    by(auto simp add: allBlocksRead_def allRdBlks_def
                      blocksOf_def)
qed

lemma  HEndPhase0_HInv4d_p:
  assumes act: "HEndPhase0 s s' p"
  and inv: "HInv4d s p"
  and inv2c: "Inv2c s"
  and inv1: "Inv1 s"
  shows "HInv4d s' p"
proof(clarsimp simp add: HInv4d_def)
  fix bk
  assume bk: "bk \<in> blocksOf s' p"
  from subsetD[OF HEndPhase0_blocksOf[OF act] bk] 
  have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s d p)"
  proof
    assume bk: "bk \<in> blocksOf s p"
    with inv
    show ?thesis
      by(auto simp add: HInv4d_def)
  next
    assume bk: "bk\<in> {dblock s' p}"
    from inv2c 
    have inv2c_inner: "Inv2c_inner s p"
      by(auto simp add: Inv2c_def)
    from bk  HEndPhase0_some[OF act inv1] 
         HEndPhase0_blocksOf2[OF act inv2c_inner] act
    have "bal bk \<in> bal `(blocksOf s p)"
      by(auto simp add: EndPhase0_def)
    with inv
    show ?thesis
      by(auto simp add: HInv4d_def)
  qed
  with act
  show "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal (disk s' d p)"
    by(auto simp add: EndPhase0_def)
qed

lemma HEndPhase0_HInv4d_q:
  assumes act: "HEndPhase0 s  s' p"
  and inv: "HInv4d s q"
  and pnq: "p\<noteq>q"
  shows "HInv4d s' q"
proof - 
 from act pnq
  have "dblock s' q = dblock s q \<and> disk s' = disk s"
    by(auto simp add: EndPhase0_def)
  moreover
  from act pnq
  have "\<forall>p d. rdBy s' q p d \<subseteq> rdBy s q p d"
    by(auto simp add: EndPhase0_def InitializePhase_def rdBy_def)
  hence "(UN p d. rdBy s' q p d) \<subseteq> (UN p d. rdBy s q p d)"
    by(auto, blast)
  ultimately
  have "blocksOf s' q \<subseteq> blocksOf s q"
    by(auto simp add: blocksOf_def, blast)
  from subsetD[OF this] inv
  have "\<forall>bk\<in>blocksOf s' q.
           \<exists>D\<in>MajoritySet. \<forall>d\<in>D. bal bk \<le> mbal(disk s d q)"
    by(auto simp add: HInv4d_def)
  with act
  show ?thesis
  by(auto simp add: EndPhase0_def HInv4d_def)
qed

theorem HEndPhase0_HInv4d:
  "\<lbrakk> HEndPhase0 s s' p; HInv4d s q; 
     Inv2c s; Inv1 s\<rbrakk> \<Longrightarrow> HInv4d s' q"
  by(blast dest: HEndPhase0_HInv4d_p HEndPhase0_HInv4d_q)

text\<open>Since we have already proved $HInv2$ is an invariant of $HNext$,
$HInv1 \wedge HInv2 \wedge HInv4$ is also an invariant of $HNext$. 
\<close>
  
lemma I2d:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s \<and> HInv2 s \<and> HInv2 s' \<and> HInv4 s"
  shows "HInv4 s'"
 proof(auto simp add: HInv4_def)
   fix p
   show "HInv4a s' p" using assms
     by(auto simp add: HInv4_def HNext_def Next_def,
        auto simp add: HInv2_def intro: HStartBallot_HInv4a,
        auto intro: HPhase0Read_HInv4a,
        auto intro: HPhase1or2Write_HInv4a,
        auto simp add: Phase1or2Read_def
             intro: HPhase1or2ReadThen_HInv4a
                    HPhase1or2ReadElse_HInv4a,
        auto simp add: EndPhase1or2_def
             intro: HEndPhase1_HInv4a
                    HEndPhase2_HInv4a,
        auto intro: HFail_HInv4a,
        auto intro: HEndPhase0_HInv4a simp add: HInv1_def)
   show "HInv4b s' p" using assms
     by(auto simp add: HInv4_def HNext_def Next_def,
        auto simp add: HInv2_def 
             intro: HStartBallot_HInv4b,
        auto intro: HPhase0Read_HInv4b,
        auto intro: HPhase1or2Write_HInv4b,
        auto simp add: Phase1or2Read_def
             intro: HPhase1or2ReadThen_HInv4b
                    HPhase1or2ReadElse_HInv4b,
        auto simp add: EndPhase1or2_def
             intro: HEndPhase1_HInv4b
                    HEndPhase2_HInv4b,
        auto intro: HFail_HInv4b,
        auto intro: HEndPhase0_HInv4b simp add: HInv1_def Inv2c_def)
   show "HInv4c s' p" using assms
     by(auto simp add: HInv4_def HNext_def Next_def,
        auto simp add: HInv2_def 
             intro: HStartBallot_HInv4c,
        auto intro: HPhase0Read_HInv4c,
        auto intro: HPhase1or2Write_HInv4c,
        auto simp add: Phase1or2Read_def
             intro: HPhase1or2ReadThen_HInv4c
                    HPhase1or2ReadElse_HInv4c,
        auto simp add: EndPhase1or2_def
             intro: HEndPhase1_HInv4c
                    HEndPhase2_HInv4c,
        auto intro: HFail_HInv4c,
        auto intro: HEndPhase0_HInv4c simp add: HInv1_def)
   show "HInv4d s' p " using assms
     by(auto simp add: HInv4_def HNext_def Next_def,
        auto simp add: HInv2_def 
             intro: HStartBallot_HInv4d,
        auto intro: HPhase0Read_HInv4d,
        auto intro: HPhase1or2Write_HInv4d,
        auto simp add: Phase1or2Read_def
             intro: HPhase1or2ReadThen_HInv4d
                    HPhase1or2ReadElse_HInv4d,
        auto simp add: EndPhase1or2_def
             intro: HEndPhase1_HInv4d
                    HEndPhase2_HInv4d,
        auto intro: HFail_HInv4d,
        auto intro: HEndPhase0_HInv4d simp add: HInv1_def)
qed

end



