(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

section "Proof of Disk Paxos' Invariant"

theory DiskPaxos_Inv1 imports DiskPaxos_Model begin

subsection \<open>Invariant 1\<close>

text\<open>This is just a type Invariant.\<close>

definition Inv1 :: "state \<Rightarrow> bool"
where
  "Inv1 s = (\<forall>p.
     inpt s p \<in> Inputs
   \<and> phase s p \<le> 3
   \<and> finite (allRdBlks s p))"

definition HInv1 :: "state \<Rightarrow> bool"
where
  "HInv1 s =
     (Inv1 s
    \<and> allInput s \<subseteq> Inputs)"

declare HInv1_def [simp]

text \<open>
  We added the assertion that the set $allRdBlks p$ is finite
  for every process $p$; one may therefore choose a block with a
  maximum ballot number in action $EndPhase1$.
\<close>

text \<open>
  With the following the lemma, it will be enough to prove 
  Inv1 s' for every action, without taking the history variables in account.
\<close>

lemma HNextPart_Inv1: "\<lbrakk> HInv1 s; HNextPart s s'; Inv1 s' \<rbrakk> \<Longrightarrow> HInv1 s'"
  by(auto simp add: HNextPart_def Inv1_def)

theorem HInit_HInv1: "HInit s \<longrightarrow> HInv1 s"
  by(auto simp add: HInit_def Inv1_def Init_def allRdBlks_def)

lemma allRdBlks_finite: 
  assumes inv: "HInv1 s" 
  and     asm: "\<forall>p. allRdBlks s' p \<subseteq> insert bk (allRdBlks s p)"
  shows   "\<forall>p. finite (allRdBlks s' p)"
proof
  fix pp
  from inv
  have "\<forall>p. finite (allRdBlks s p)"
    by(simp add: Inv1_def)
  hence "finite (allRdBlks s pp)"
    by blast
  with asm 
  show "finite (allRdBlks s' pp)"
    by (auto intro: finite_subset)
qed

theorem HPhase1or2ReadThen_HInv1:
  assumes inv1: "HInv1 s"
  and act: "HPhase1or2ReadThen s s' p d q"
  shows "HInv1 s'"
proof -
  \<comment> \<open>we focus on the last conjunct of Inv1\<close>
  from act
  have "\<forall>p. allRdBlks s' p \<subseteq> allRdBlks s p \<union> {\<lparr>block = disk s d q, proc = q\<rparr>}"
    by(auto simp add: Phase1or2ReadThen_def allRdBlks_def
               split: if_split_asm)
  with inv1
  have "\<forall>p. finite (allRdBlks s' p)"
    by(blast dest: allRdBlks_finite)
  \<comment> \<open>the others conjuncts are trivial\<close>
  with inv1 act
  show ?thesis
    by(auto simp add: Inv1_def Phase1or2ReadThen_def HNextPart_def) 
qed

theorem HEndPhase1_HInv1: 
  assumes inv1: "HInv1 s" 
  and act: "HEndPhase1 s s' p"
  shows "HInv1 s'"
proof -
     from inv1 act 
     have "Inv1 s'" 
       by(auto simp add:  Inv1_def EndPhase1_def InitializePhase_def allRdBlks_def)
     with inv1 act 
     show ?thesis 
       by(auto simp del: HInv1_def dest: HNextPart_Inv1)
qed

theorem HStartBallot_HInv1:
  assumes inv1: "HInv1 s"
  and act: "HStartBallot s s' p"
  shows "HInv1 s'"
 proof -
     from inv1 act 
     have "Inv1 s'" 
       by(auto simp add: Inv1_def StartBallot_def InitializePhase_def allRdBlks_def)
     with inv1 act 
     show ?thesis 
       by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

theorem HPhase1or2Write_HInv1:
  assumes inv1: "HInv1 s"
  and act: "HPhase1or2Write s s' p d"
  shows "HInv1 s'"
proof -
 from inv1 act 
 have "Inv1 s'"
   by(auto simp add: Inv1_def Phase1or2Write_def allRdBlks_def)
 with inv1 act 
 show ?thesis
   by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

theorem HPhase1or2ReadElse_HInv1: 
  assumes act: "HPhase1or2ReadElse s s' p d q"
  and inv1: "HInv1 s"
  shows "HInv1 s'"
  using HStartBallot_HInv1[OF inv1] act
  by(auto simp add: Phase1or2ReadElse_def)

theorem HEndPhase2_HInv1:
  assumes inv1: "HInv1 s"
  and  act: "HEndPhase2 s s' p"
  shows "HInv1 s'"
proof -
  from inv1 act 
  have "Inv1 s'"
    by(auto simp add: Inv1_def EndPhase2_def InitializePhase_def allRdBlks_def)
  with inv1 act 
  show ?thesis
    by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

theorem HFail_HInv1: 
  assumes inv1: "HInv1 s" 
  and     act: "HFail s s' p"
  shows "HInv1 s'"
proof -
  from inv1 act 
  have "Inv1 s'"
    by(auto simp add: Inv1_def Fail_def InitializePhase_def allRdBlks_def)
  with inv1 act show ?thesis
  by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

theorem HPhase0Read_HInv1:
  assumes inv1: "HInv1 s"
  and     act: "HPhase0Read s s' p d"
  shows "HInv1 s'"
proof -
 \<comment> \<open>we focus on the last conjunct of Inv1\<close>
  from act
  have "\<forall>pp. allRdBlks s' pp \<subseteq> allRdBlks s pp \<union> {\<lparr>block = disk s d p, proc = p\<rparr>}"
    by(auto simp add: Phase0Read_def allRdBlks_def
               split: if_split_asm)
  with inv1
  have "\<forall>p. finite (allRdBlks s' p)"
      by(blast dest: allRdBlks_finite)
  \<comment> \<open>the others conjuncts are trivial\<close>
  with inv1 act
  have "Inv1 s'"
    by(auto simp add: Inv1_def Phase0Read_def)
  with inv1 act
  show ?thesis
  by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

theorem HEndPhase0_HInv1: 
  assumes inv1: "HInv1 s"
  and act: "HEndPhase0 s s' p"
  shows "HInv1 s'"
proof -
  from inv1 act
  have "Inv1 s'"
    by(auto simp add: Inv1_def EndPhase0_def allRdBlks_def InitializePhase_def)
  with inv1 act
  show ?thesis
    by(auto simp del: HInv1_def elim: HNextPart_Inv1)
qed

declare HInv1_def [simp del]

text \<open>$HInv1$ is an invariant of $HNext$\<close>
 
lemma I2a:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s"
  shows "HInv1 s'"
  using assms
  by(auto
    simp add: HNext_def Next_def,
    auto intro: HStartBallot_HInv1,
    auto intro: HPhase0Read_HInv1,
    auto intro: HPhase1or2Write_HInv1,
    auto simp add: Phase1or2Read_def
         intro: HPhase1or2ReadThen_HInv1
                HPhase1or2ReadElse_HInv1,
    auto simp add: EndPhase1or2_def
         intro: HEndPhase1_HInv1
                HEndPhase2_HInv1,
    auto intro: HFail_HInv1,
    auto intro: HEndPhase0_HInv1)


end
