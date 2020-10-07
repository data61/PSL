(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Inv5 imports DiskPaxos_Inv3 DiskPaxos_Inv4 begin

subsection \<open>Invariant 5\<close>

text \<open>
  This invariant asserts that, if a processor $p$ is in phase 2, 
  then either its $bal$ and $inp$ values satisfy $maxBalInp$, or
  else $p$ must eventually abort its current ballot. Processor $p$ 
  will eventually abort its ballot if there is some processor $q$
  and majority set $D$ such that $p$ has not read $q$'s block on 
  any disk $D$, and all of those blocks have $mbal$ values greater
  than $bal(dblock s p)$.
\<close>

definition maxBalInp :: "state \<Rightarrow> nat \<Rightarrow> InputsOrNi \<Rightarrow> bool"
  where "maxBalInp s b v = (\<forall>bk\<in>allBlocks s. b \<le> bal bk \<longrightarrow> inp bk = v)"

definition HInv5_inner_R :: "state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "HInv5_inner_R s p =
          (maxBalInp s (bal(dblock s p)) (inp(dblock s p))
        \<or> (\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.  bal(dblock s p) < mbal(disk s d q)
                                      \<and> \<not>hasRead s p d q)))"

definition HInv5_inner :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "HInv5_inner s p = (phase s p = 2 \<longrightarrow> HInv5_inner_R s p)"

definition HInv5 :: "state \<Rightarrow> bool"
  where "HInv5 s = (\<forall>p. HInv5_inner s p)"

subsubsection \<open>Proof of Invariant 5\<close>


text \<open>The initial state implies Invariant 5.\<close>

theorem HInit_HInv5: "HInit s \<Longrightarrow> HInv5 s"
  using Disk_isMajority
  by(auto simp add: HInit_def Init_def HInv5_def HInv5_inner_def)

text \<open>
  We will use the notation used in the proofs of invariant 4, and prove
the lemma $action$-$HInv5$-$p$ and $action$-$HInv5$-$q$ for each action, for
the cases $p=q$ and $p\not = q$ respectively.

  Also, for each action we will define an $action$-$allBlocks$ lemma in the 
same way that we defined -$blocksOf$ lemmas in the proofs of $HInv2$. Now we prove 
that for each action the new $allBlocks$ are included in the old $allBlocks$ or, in
some cases, included in the old $allBlocks$ union the new $dblock$. 
\<close>

lemma HStartBallot_HInv5_p:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv5_inner s p"
  shows "HInv5_inner s' p" using assms
  by(auto simp add: StartBallot_def HInv5_inner_def)

lemma  HStartBallot_blocksOf_q:
  assumes act: "HStartBallot s s' p"
  and pnq: "p\<noteq>q"
  shows "blocksOf s' q \<subseteq> blocksOf s q" using assms
  by(auto simp add: StartBallot_def InitializePhase_def blocksOf_def rdBy_def)

lemma HStartBallot_allBlocks:
  assumes act: "HStartBallot s s' p"
  shows "allBlocks s' \<subseteq> allBlocks s \<union> {dblock s' p}"
proof(auto simp del: HStartBallot_def simp add: allBlocks_def
           dest: HStartBallot_blocksOf_q[OF act])
  fix x pa
  assume x_pa: "x \<in> blocksOf s' pa" and
         x_nblks: "\<forall>xa. x \<notin> blocksOf s xa"
  show "x=dblock s' p"
  proof(cases "p=pa")
    case True
    from x_nblks
    have "x \<notin> blocksOf s p"
      by auto
    with True subsetD[OF HStartBallot_blocksOf[OF act] x_pa]
    show ?thesis
      by auto
  next
    case False
    from x_nblks subsetD[OF HStartBallot_blocksOf_q[OF act False] x_pa]
    show ?thesis
      by auto
  qed
qed
   
lemma HStartBallot_HInv5_q1:
  assumes act: "HStartBallot s s' p"
  and pnq: "p\<noteq>q"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
proof(auto simp add: maxBalInp_def)
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and bal: "bal (dblock s' q) \<le> bal bk"
  from act pnq
  have dblock': "dblock s' q = dblock s q" by(auto simp add: StartBallot_def)
  from subsetD[OF HStartBallot_allBlocks[OF act] bk]
  show "inp bk = inp (dblock s' q)"
  proof
    assume bk: "bk \<in> allBlocks s"
    with inv5_1 dblock' bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    have "dblock s p \<in> allBlocks s"
      by(auto simp add: allBlocks_def blocksOf_def)
    with bal act bk dblock' inv5_1
    show ?thesis
      by(auto simp add: maxBalInp_def StartBallot_def)
  qed
qed

lemma HStartBallot_HInv5_q2:
  assumes act: "HStartBallot s s' p"
  and pnq: "p\<noteq>q"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from act pnq
  have  disk: "disk s' = disk s"
    and blocksRead: "\<forall>d. blocksRead s' q d = blocksRead s q d"
    and dblock: "dblock s' q = dblock s q"
    by(auto simp add: StartBallot_def InitializePhase_def)
  with inv5_2
  show ?thesis
    by(auto simp add: hasRead_def)
qed

lemma HStartBallot_HInv5_q:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv5_inner s q"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
  using assms and HStartBallot_HInv5_q1[OF act pnq] HStartBallot_HInv5_q2[OF act pnq]
  by(auto simp add: HInv5_inner_def HInv5_inner_R_def StartBallot_def)

theorem HStartBallot_HInv5:
  "\<lbrakk> HStartBallot s s' p; HInv5_inner s q \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
by(blast dest: HStartBallot_HInv5_q HStartBallot_HInv5_p)


lemma HPhase1or2Write_HInv5_1:
  assumes act: "HPhase1or2Write s s' p d"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
  using assms and HPhase1or2Write_blocksOf[OF act]
  by(auto simp add: Phase1or2Write_def maxBalInp_def allBlocks_def)

lemma HPhase1or2Write_HInv5_p2:
  assumes act: "HPhase1or2Write s s' p d"
  and inv4c: "HInv4c s p"
  and phase: "phase s p = 2"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s p) < mbal(disk s d q)
                                     \<and> \<not>hasRead s p d q)"
  shows "\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s' p) < mbal(disk s' d q)
                                     \<and> \<not>hasRead s' p d q)" 
proof -
  from inv5_2
  obtain D q 
    where i1: "IsMajority D"
      and i2: "\<forall>d\<in>D. bal(dblock s p) < mbal(disk s d q)"
      and i3: "\<forall>d\<in>D. \<not>hasRead s p d q"
    by(auto simp add: MajoritySet_def)
  have pnq: "p\<noteq>q"
  proof -
    from inv4c phase 
    obtain D1 where r1: "IsMajority D1 \<and> (\<forall>d\<in>D1. mbal(disk s d p) = bal (dblock s p))"
      by(auto simp add: HInv4c_def MajoritySet_def)
    with i1 majorities_intersect
    have "D\<inter>D1\<noteq>{}" by auto
    then obtain dd where  "dd\<in>D\<inter>D1"
      by auto
    with i1 i2 r1
    have "bal(dblock s p) < mbal(disk s dd q) \<and> mbal(disk s dd p) = bal (dblock s p)"
      by auto
    thus ?thesis by auto
  qed
  from act pnq
      \<comment> \<open>$dblock$ and $hasRead$ do not change\<close>
  have  "dblock s' = dblock s"
    and "\<forall>d. hasRead s' p d q = hasRead s p d q"
      \<comment> \<open>In all disks $q$ blocks don't change\<close>
    and "\<forall>d. disk s' d q = disk s d q"
    by(auto simp add: Phase1or2Write_def hasRead_def)
  with i2 i1 i3 majority_nonempty
  have "\<forall>d\<in>D. bal (dblock s' p) < mbal (disk s' d q) \<and> \<not>hasRead s' p d q"
    by auto
  with i1 
  show ?thesis
    by(auto simp add: MajoritySet_def)
qed  

lemma HPhase1or2Write_HInv5_p:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv5_inner s p"
  and inv4: "HInv4c s p"
  shows "HInv5_inner s' p"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' p = 2"
    and i2: "\<forall>D\<in>MajoritySet. \<forall>q. \<exists>d\<in>D. bal (dblock s' p) < mbal (disk s' d q) \<longrightarrow> hasRead s' p d q"
  with act have phase: "phase s p = 2" 
    by(auto simp add: Phase1or2Write_def)
  show "maxBalInp s' (bal (dblock s' p)) (inp (dblock s' p))"
  proof(rule HPhase1or2Write_HInv5_1[OF act, of p])
    from HPhase1or2Write_HInv5_p2[OF act inv4 phase] inv i2 phase
    show "maxBalInp s (bal (dblock s p)) (inp (dblock s p))"
      by(auto simp add: HInv5_inner_def HInv5_inner_R_def, blast)
  qed
qed

lemma HPhase1or2Write_allBlocks:
  assumes act: "HPhase1or2Write s s' p d"
  shows "allBlocks s' \<subseteq> allBlocks s"
  using HPhase1or2Write_blocksOf[OF act]
  by(auto simp add: allBlocks_def)
   
lemma HPhase1or2Write_HInv5_q2:
  assumes act: "HPhase1or2Write s s' p d"
  and pnq: "p\<noteq>q"
  and inv4a: "HInv4a s p"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from inv5_2
  obtain D qq 
    where i1: "IsMajority D"
      and i2: "\<forall>d\<in>D. bal(dblock s q) < mbal(disk s d qq)"
      and i3: "\<forall>d\<in>D. \<not>hasRead s q d qq"
    by(auto simp add: MajoritySet_def)
  from act pnq
      \<comment> \<open>$dblock$ and $hasRead$ do not change\<close>
  have  dblock': "dblock s' = dblock s"
    and hasread: "\<forall>d. hasRead s' q d qq = hasRead s q d qq"
    by(auto simp add: Phase1or2Write_def hasRead_def)
  have "\<forall>d\<in>D. bal (dblock s' q) < mbal (disk s' d qq) \<and> \<not>hasRead s' q d qq"
  proof(cases "qq=p")
    case True
    have "bal(dblock s q) < mbal(dblock s p)"
    proof -
      from inv4a act i1
      have "\<exists>d\<in>D. mbal(disk s d p) \<le> mbal(dblock s p)"
        by(auto simp add: MajoritySet_def HInv4a_def 
                          HInv4a2_def Phase1or2Write_def)
      with True i2
      show "bal(dblock s q) < mbal(dblock s p)"
        by auto
    qed
    with hasread dblock' True i1 i2 i3 act
    show ?thesis
      by(auto simp add: Phase1or2Write_def)
  next
    case False
    with act i2 i3
    show ?thesis
      by(auto simp add: Phase1or2Write_def hasRead_def)
  qed
  with i1 
  show ?thesis
    by(auto simp add: MajoritySet_def)
qed  

lemma HPhase1or2Write_HInv5_q:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv5_inner s q"
  and inv4a: "HInv4a s p"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' q = 2"
    and i2: "\<forall>D\<in>MajoritySet. \<forall>qa. \<exists>d\<in>D. bal (dblock s' q) < mbal (disk s' d qa) \<longrightarrow> hasRead s' q d qa"
  from phase' act have phase: "phase s q = 2" 
    by(auto simp add: Phase1or2Write_def)
  show "maxBalInp s' (bal (dblock s' q)) (inp (dblock s' q))"
  proof(rule HPhase1or2Write_HInv5_1[OF act, of q])
    from HPhase1or2Write_HInv5_q2[OF act pnq inv4a] inv i2 phase
    show "maxBalInp s (bal (dblock s q)) (inp (dblock s q))"
      by(auto simp add: HInv5_inner_def HInv5_inner_R_def, blast)
  qed
qed

theorem HPhase1or2Write_HInv5:
  "\<lbrakk> HPhase1or2Write s s' p d; HInv5_inner s q; 
     HInv4c s p; HInv4a s p \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
  by(blast dest: HPhase1or2Write_HInv5_q HPhase1or2Write_HInv5_p)

lemma HPhase1or2ReadThen_HInv5_1:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
  using assms and HPhase1or2ReadThen_blocksOf[OF act]
  by(auto simp add: Phase1or2ReadThen_def maxBalInp_def allBlocks_def)

lemma HPhase1or2ReadThen_HInv5_p2:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv4c: "HInv4c s p"
  and inv2c: "Inv2c_inner s p"
  and phase: "phase s p = 2"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s p) < mbal(disk s d q)
                                     \<and> \<not>hasRead s p d q)"
  shows "\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s' p) < mbal(disk s' d q)
                                     \<and> \<not>hasRead s' p d q)" 
proof -
  from inv5_2
  obtain D q 
    where i1: "IsMajority D"
      and i2: "\<forall>d\<in>D. bal(dblock s p) < mbal(disk s d q)"
      and i3: "\<forall>d\<in>D. \<not>hasRead s p d q"
    by(auto simp add: MajoritySet_def)
  from inv2c phase
  have "bal(dblock s p)=mbal(dblock s p)"
    by(auto simp add: Inv2c_inner_def)
  moreover
  from act have "mbal (disk s d r) < mbal (dblock s p)" 
    by(auto simp add: Phase1or2ReadThen_def)
  moreover
  from i2 have "d\<in>D \<longrightarrow> bal(dblock s p) < mbal(disk s d q)" by auto
  ultimately have pnr: "d\<in>D \<longrightarrow> q\<noteq>r" by auto
  have pnq: "p\<noteq>q"
  proof -
    from inv4c phase 
    obtain D1 where r1: "IsMajority D1 \<and> (\<forall>d\<in>D1. mbal(disk s d p) = bal (dblock s p))"
      by(auto simp add: HInv4c_def MajoritySet_def)
    with i1 majorities_intersect
    have "D\<inter>D1\<noteq>{}" by auto
    then obtain dd where  "dd\<in>D\<inter>D1"
      by auto
    with i1 i2 r1
    have "bal(dblock s p) < mbal(disk s dd q) \<and> mbal(disk s dd p) = bal (dblock s p)"
      by auto
    thus ?thesis by auto
  qed
  from pnr act
  have hasRead': "\<forall>d\<in>D. hasRead s' p d q = hasRead s p d q"
    by(auto simp add: Phase1or2ReadThen_def hasRead_def) 
  from act pnq
      \<comment> \<open>$dblock$ and $disk$ do not change\<close>
  have  "dblock s' = dblock s"
    and "\<forall>d. disk s' = disk s"
    by(auto simp add: Phase1or2ReadThen_def)
  with i2 hasRead' i3
  have "\<forall>d\<in>D. bal (dblock s' p) < mbal (disk s' d q) \<and> \<not>hasRead s' p d q"
    by auto
  with i1 
  show ?thesis
    by(auto simp add: MajoritySet_def)
qed  

lemma HPhase1or2ReadThen_HInv5_p:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv5_inner s p"
  and inv4: "HInv4c s p"
  and inv2c: "Inv2c s"
  shows "HInv5_inner s' p"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' p = 2"
    and i2: "\<forall>D\<in>MajoritySet. \<forall>q. \<exists>d\<in>D. bal (dblock s' p) < mbal (disk s' d q) \<longrightarrow> hasRead s' p d q"
  with act have phase: "phase s p = 2" 
    by(auto simp add: Phase1or2ReadThen_def)
  show "maxBalInp s' (bal (dblock s' p)) (inp (dblock s' p))"
  proof(rule HPhase1or2ReadThen_HInv5_1[OF act, of p])
    from inv2c
    have "Inv2c_inner s p" by(auto simp add: Inv2c_def)
    from HPhase1or2ReadThen_HInv5_p2[OF act inv4 this phase] inv i2 phase
    show "maxBalInp s (bal (dblock s p)) (inp (dblock s p))"
      by(auto simp add: HInv5_inner_def HInv5_inner_R_def, blast)
  qed
qed

lemma HPhase1or2ReadThen_allBlocks:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  shows "allBlocks s' \<subseteq> allBlocks s"
  using HPhase1or2ReadThen_blocksOf[OF act]
  by(auto simp add: allBlocks_def)
   
lemma HPhase1or2ReadThen_HInv5_q2:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and pnq: "p\<noteq>q"
  and inv4a: "HInv4a s p"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from inv5_2
  obtain D qq 
    where i1: "IsMajority D"
      and i2: "\<forall>d\<in>D. bal(dblock s q) < mbal(disk s d qq)"
      and i3: "\<forall>d\<in>D. \<not>hasRead s q d qq"
    by(auto simp add: MajoritySet_def)
  from act pnq
      \<comment> \<open>$dblock$ and $hasRead$ do not change\<close>
  have  dblock': "dblock s' = dblock s"
    and   disk': "disk s' = disk s" 
    and hasread: "\<forall>d. hasRead s' q d qq = hasRead s q d qq"
    by(auto simp add: Phase1or2ReadThen_def hasRead_def)
  with i2 i3
  have "\<forall>d\<in>D. bal (dblock s' q) < mbal (disk s' d qq) \<and> \<not>hasRead s' q d qq"
    by auto
  with i1 
  show ?thesis
    by(auto simp add: MajoritySet_def)
qed  

lemma HPhase1or2ReadThen_HInv5_q:
  assumes act: "HPhase1or2ReadThen s s' p d r"
  and inv: "HInv5_inner s q"
  and inv4a: "HInv4a s p"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' q = 2"
    and i2: "\<forall>D\<in>MajoritySet. \<forall>qa. \<exists>d\<in>D. bal (dblock s' q) < mbal (disk s' d qa) \<longrightarrow> hasRead s' q d qa"
  from phase' act have phase: "phase s q = 2" 
    by(auto simp add: Phase1or2ReadThen_def)
  show "maxBalInp s' (bal (dblock s' q)) (inp (dblock s' q))"
  proof(rule HPhase1or2ReadThen_HInv5_1[OF act, of q])
    from HPhase1or2ReadThen_HInv5_q2[OF act pnq inv4a] inv i2 phase
    show "maxBalInp s (bal (dblock s q)) (inp (dblock s q))"
      by(auto simp add: HInv5_inner_def HInv5_inner_R_def, blast)
  qed
qed

theorem HPhase1or2ReadThen_HInv5:
  "\<lbrakk> HPhase1or2ReadThen s s' p d r; HInv5_inner s q; 
     Inv2c s; HInv4c s p; HInv4a s p \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
  by(blast dest: HPhase1or2ReadThen_HInv5_q HPhase1or2ReadThen_HInv5_p)

theorem HPhase1or2ReadElse_HInv5:
  "\<lbrakk> HPhase1or2ReadElse s s' p d r; HInv5_inner s q \<rbrakk>
     \<Longrightarrow> HInv5_inner s' q"
  using HStartBallot_HInv5
  by(auto simp add: Phase1or2ReadElse_def)

lemma HEndPhase2_HInv5_p:
  "HEndPhase2 s s' p  \<Longrightarrow> HInv5_inner s' p"
  by(auto simp add: EndPhase2_def HInv5_inner_def)

lemma HEndPhase2_allBlocks:
  assumes act: "HEndPhase2 s s' p"
  shows "allBlocks s' \<subseteq> allBlocks s"
  using HEndPhase2_blocksOf[OF act]
  by(auto simp add: allBlocks_def)
   
lemma HEndPhase2_HInv5_q1:
  assumes act: "HEndPhase2 s s' p"
  and pnq: "p\<noteq>q"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
proof(auto simp add: maxBalInp_def)
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and bal: "bal (dblock s' q) \<le> bal bk"
  from act pnq
  have dblock': "dblock s' q = dblock s q" by(auto simp add: EndPhase2_def)
  from subsetD[OF HEndPhase2_allBlocks[OF act] bk] inv5_1 dblock' bal
  show "inp bk = inp (dblock s' q)"
      by(auto simp add: maxBalInp_def)
qed

lemma HEndPhase2_HInv5_q2:
  assumes act: "HEndPhase2 s s' p"
  and pnq: "p\<noteq>q"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from act pnq
  have  disk: "disk s' = disk s"
    and blocksRead: "\<forall>d. blocksRead s' q d = blocksRead s q d"
    and dblock: "dblock s' q = dblock s q"
    by(auto simp add: EndPhase2_def InitializePhase_def)
  with inv5_2
  show ?thesis
    by(auto simp add: hasRead_def)
qed

lemma HEndPhase2_HInv5_q:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv5_inner s q"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
  using assms and HEndPhase2_HInv5_q1[OF act pnq] HEndPhase2_HInv5_q2[OF act pnq]
  by(auto simp add: HInv5_inner_def HInv5_inner_R_def EndPhase2_def)

theorem HEndPhase2_HInv5:
  "\<lbrakk> HEndPhase2 s s' p; HInv5_inner s q \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
  by(blast dest: HEndPhase2_HInv5_q HEndPhase2_HInv5_p)

lemma HEndPhase1_HInv5_p:
  assumes act: "HEndPhase1 s s' p"
  and inv4: "HInv4 s"
  and inv2a: "Inv2a s"
  and inv2a': "Inv2a s'"
  and inv2c: "Inv2c s"
  and asm4: "\<not>maxBalInp s' (bal(dblock s' p)) (inp(dblock s' p))"
  shows "(\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s' p) < mbal(disk s' d q)
                                     \<and> \<not>hasRead s' p d q))"
proof -
  have "\<exists>bk\<in>allBlocks s. bal(dblock s' p) \<le> bal bk \<and> bk \<noteq> dblock s' p"
  proof -
    from asm4
    obtain bk
      where p31: "bk\<in>allBlocks s' \<and>  bal(dblock s' p) \<le> bal bk \<and> bk \<noteq> dblock s' p"
      by(auto simp add: maxBalInp_def)
    then obtain q where p32: "bk \<in> blocksOf s' q"
      by(auto simp add: allBlocks_def)
    from act
    have dblock: "p\<noteq>q \<Longrightarrow> dblock s' q = dblock s q" 
      by(auto simp add: EndPhase1_def)
    have "bk \<in> blocksOf s q"
    proof(cases "p=q")
      case True
      with p32 p31 HEndPhase1_blocksOf[OF act]
      show ?thesis
        by auto
    next
      case False
      from dblock[OF False] subsetD[OF HEndPhase1_blocksOf[OF act, of q] p32]
      show ?thesis
        by(auto simp add: blocksOf_def)
    qed
    with p31
    show ?thesis
    by(auto simp add: allBlocks_def)
  qed
  then obtain bk where p22: "bk\<in>allBlocks s \<and> bal (dblock s' p) \<le> bal bk \<and> bk \<noteq> dblock s' p" by auto
  have "\<exists>q\<in>UNIV-{p}. bk \<in> blocksOf s q"
  proof -
    from p22
    obtain q where bk: "bk\<in> blocksOf s q"
      by(auto simp add: allBlocks_def)
    from act p22
    have "mbal(dblock s p) \<le> bal bk"
      by(auto simp add: EndPhase1_def)
    moreover
    from act
    have "phase s p = 1"
      by(auto simp add: EndPhase1_def)
    moreover
    from inv4
    have "HInv4b s p" by(auto simp add: HInv4_def)
    ultimately
    have "p\<noteq>q"
      using bk
      by(auto simp add: HInv4_def HInv4b_def)
    with bk
    show ?thesis
      by auto
  qed
  then obtain q where p23: "q\<in>UNIV-{p} \<and> bk \<in> blocksOf s q"
    by auto
  have "\<exists>D\<in>MajoritySet.\<forall>d\<in>D. bal(dblock s' p) \<le> mbal(disk s d q)"
  proof -
    from p23 inv4 
    have i4d: "\<exists>D\<in>MajoritySet.\<forall>d\<in>D. bal bk \<le> mbal(disk s d q)" 
      by(auto simp add: HInv4_def HInv4d_def)
    from i4d p22
    show ?thesis
      by force
  qed
  then obtain D where Dmaj: "D\<in>MajoritySet" and p24:"(\<forall>d\<in>D. bal(dblock s' p) \<le> mbal(disk s d q))"
    by auto
  have p25: "\<forall>d\<in>D. bal(dblock s' p) < mbal(disk s d q)"
  proof -
    from inv2c
    have "Inv2c_inner s p"
      by(auto simp add: Inv2c_def)
    with act
    have bal_pos: "0 < bal(dblock s' p)"
      by(auto simp add: Inv2c_inner_def EndPhase1_def)
    with inv2a'
    have "bal(dblock s' p) \<in> Ballot p \<union> {0}"
      by(auto simp add: Inv2a_def Inv2a_inner_def 
                        Inv2a_innermost_def blocksOf_def)  
    with bal_pos have bal_in_p: "bal(dblock s' p) \<in> Ballot p"
      by auto
    from inv2a have "Inv2a_inner s q" by(auto simp add: Inv2a_def)
    hence "\<forall>d\<in>D. mbal(disk s d q) \<in> Ballot q \<union> {0}"
      by(auto simp add: Inv2a_inner_def Inv2a_innermost_def 
                        blocksOf_def)
    with p24 bal_pos
    have "\<forall>d\<in>D. mbal(disk s d q) \<in> Ballot q"
      by force
    with  Ballot_disj p23 bal_in_p
    have "\<forall>d\<in>D. mbal(disk s d q)\<noteq> bal(dblock s' p)"
      by force
    with p23 p24
    show ?thesis
      by force
  qed
  with p23 act
  have "\<forall>d\<in>D. bal(dblock s' p) < mbal(disk s' d q) \<and> \<not>hasRead s' p d q"
    by(auto simp add: EndPhase1_def InitializePhase_def hasRead_def)
  with Dmaj
  show ?thesis
    by blast
qed
  
lemma union_inclusion:
 "\<lbrakk> A \<subseteq> A'; B\<subseteq> B' \<rbrakk> \<Longrightarrow> A\<union>B \<subseteq> A'\<union>B'"
by blast

lemma  HEndPhase1_blocksOf_q:
  assumes act: "HEndPhase1 s s' p"
  and pnq: "p\<noteq>q"
  shows "blocksOf s' q \<subseteq> blocksOf s q"
proof -
  from act pnq
  have dblock: "{dblock s' q} \<subseteq> {dblock s q}"
    and disk: "disk s' = disk s"
    and blks: "blocksRead s' q = blocksRead s q"
    by(auto simp add: EndPhase1_def InitializePhase_def)
  from disk
  have disk': "{disk s' d q | d . d\<in> UNIV} \<subseteq> {disk s d q | d . d\<in> UNIV}" (is "?D' \<subseteq> ?D") 
    by auto
  from pnq act
  have "(UN qq d. rdBy s' q qq d) \<subseteq> (UN qq d. rdBy s q qq d)" 
    by(auto simp add: EndPhase1_def InitializePhase_def rdBy_def split: if_split_asm, blast)
  hence "{block br | br. br \<in> (UN qq d. rdBy s' q qq d)} \<subseteq> {block br | br. br \<in> (UN qq d. rdBy s q qq d)}" (is "?R' \<subseteq> ?R")
    by auto blast
  from union_inclusion[OF dblock union_inclusion[OF disk' this]]
  show ?thesis
    by(auto simp add: blocksOf_def)  
qed

lemma HEndPhase1_allBlocks:
  assumes act: "HEndPhase1 s s' p"
  shows "allBlocks s' \<subseteq> allBlocks s \<union> {dblock s' p}"
proof(auto simp del: HEndPhase1_def simp add: allBlocks_def
           dest: HEndPhase1_blocksOf_q[OF act])
  fix x pa
  assume x_pa: "x \<in> blocksOf s' pa" and
         x_nblks: "\<forall>xa. x \<notin> blocksOf s xa"
  show "x=dblock s' p"
  proof(cases "p=pa")
    case True
    from x_nblks
    have "x \<notin> blocksOf s p"
      by auto
    with True subsetD[OF HEndPhase1_blocksOf[OF act] x_pa]
    show ?thesis
      by auto
  next
    case False
    from x_nblks subsetD[OF HEndPhase1_blocksOf_q[OF act False] x_pa]
    show ?thesis
      by auto
  qed
qed

lemma HEndPhase1_HInv5_q:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv5 s"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a s'"
  and inv2a_q: "Inv2a s"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  and inv3: "HInv3 s"
  and phase': "phase s' q = 2"
  and pnq: "p\<noteq>q"
  and asm4: "\<not>maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
  shows "(\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq))"
proof - 
  from act pnq
  have "phase s' q = phase s q"
    and phase_p: "phase s p = 1"
    and disk: "disk s' = disk s"
    and dblock: "dblock s' q = dblock s q"
    and bal: "bal(dblock s' p) = mbal(dblock s p)"
    by(auto simp add: EndPhase1_def InitializePhase_def)
  with phase'
  have phase: "phase s q = 2" by auto
  from phase inv2c
  have bal_dblk_q: "bal(dblock s q) \<in> Ballot q"
    by(auto simp add: Inv2c_def Inv2c_inner_def)
  have "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  proof(cases "maxBalInp s (bal(dblock s q)) (inp(dblock s q))")
    case True
    have p21: "bal(dblock s q) < bal(dblock s' p) \<and> inp(dblock s q) \<noteq> inp(dblock s' p)"
    proof -
      from True asm4 dblock HEndPhase1_allBlocks[OF act]
      have p32: "  bal(dblock s q)\<le> bal(dblock s' p) 
                 \<and> inp(dblock s q) \<noteq> inp(dblock s' p)"
        by(auto simp add: maxBalInp_def)
      from inv2a
      have "bal(dblock s' p) \<in> Ballot p \<union> {0}"
        by(auto simp add: Inv2a_def Inv2a_inner_def 
                          Inv2a_innermost_def blocksOf_def)
      moreover
      from Ballot_disj Ballot_nzero pnq
      have "Ballot q \<inter> (Ballot p \<union> {0}) = {}"
        by auto
      ultimately
      have "bal(dblock s' p) \<noteq> bal(dblock s q)"
        using bal_dblk_q
        by auto
      with p32
      show ?thesis
        by auto
    qed
    have "\<exists>D\<in>MajoritySet.\<forall>d\<in>D. bal(dblock s q) < mbal(disk s d p) \<and> hasRead s p d q"
    proof -
      from  act
      have "\<exists>D\<in>MajoritySet.\<forall>d\<in>D. d\<in>disksWritten s p \<and> (\<forall>q\<in>UNIV-{p}. hasRead s p d q)"
        by(auto simp add: EndPhase1_def MajoritySet_def)
      then obtain D
        where act1: "\<forall>d\<in>D. d\<in>disksWritten s p \<and> (\<forall>q\<in>UNIV-{p}. hasRead s p d q)"
        and Dmaj: "D\<in>MajoritySet"
        by auto
      from inv2b
      have "\<forall>d. Inv2b_inner s p d" by(auto simp add: Inv2b_def)
      with act1 pnq phase_p bal
      have "\<forall>d\<in>D. bal(dblock s' p)= mbal(disk s d p) \<and> hasRead s p d q" 
        by(auto simp add: Inv2b_def Inv2b_inner_def)
      with p21 Dmaj
      have "\<forall>d\<in>D. bal(dblock s q)< mbal(disk s d p) \<and> hasRead s p d q"
        by auto
      with Dmaj
      show ?thesis
        by auto
    qed
    then obtain D
      where p22: "D\<in>MajoritySet \<and> (\<forall>d\<in>D. bal(dblock s q) < mbal(disk s d p) \<and> hasRead s p d q)"
      by auto
    have p23: "\<forall>d\<in>D.\<lparr>block=dblock s q, proc=q\<rparr> \<notin> blocksRead s p d"
    proof -
      have "dblock s q \<in> allBlocksRead s p \<longrightarrow> inp(dblock s' p) = inp(dblock s q)"
      proof auto
        assume dblock_q: "dblock s q \<in> allBlocksRead s p"
        from inv2a_q
        have "(bal(dblock s q)=0) = (inp (dblock s q) = NotAnInput)"
          by(auto simp add: Inv2a_def Inv2a_inner_def 
                            blocksOf_def Inv2a_innermost_def)
        with bal_dblk_q Ballot_nzero dblock_q InputsOrNi
        have dblock_q_nib: "dblock s q \<in> nonInitBlks s p"
          by(auto simp add: nonInitBlks_def blocksSeen_def)
        with act
        have dblock_max: "inp(dblock s' p)=inp(maxBlk s p)"
          by(auto simp add: EndPhase1_def)
        from maxBlk_in_nonInitBlks[OF dblock_q_nib inv1]
        have max_in_nib: "maxBlk s p \<in> nonInitBlks s p" ..
        hence "nonInitBlks s p \<subseteq> allBlocks s"
          by(auto simp add: allBlocks_def nonInitBlks_def 
                            blocksSeen_def blocksOf_def rdBy_def 
                            allBlocksRead_def allRdBlks_def)
        with True subsetD[OF this max_in_nib]
        have "bal (dblock s q) \<le> bal (maxBlk s p) \<longrightarrow> inp (maxBlk s p) = inp (dblock s q)"
          by(auto simp add: maxBalInp_def)
        with maxBlk_in_nonInitBlks[OF dblock_q_nib inv1] 
             dblock_q_nib dblock_max
        show "inp(dblock s' p) = inp(dblock s q)"
          by auto
      qed
      with p21
      have "dblock s q \<notin> block ` allRdBlks s p"
        by(auto simp add: allBlocksRead_def)
      hence "\<forall>d. dblock s q \<notin> block ` blocksRead s p d"
        by(auto simp add: allRdBlks_def)
      thus ?thesis
        by force
    qed
    have p24: "\<forall>d\<in>D. \<not> (\<exists>br\<in> blocksRead s q d. bal(dblock s q) \<le> mbal (block br))"
    proof -
      from inv2c phase
      have "\<forall>d. \<forall>br\<in>blocksRead s q d. mbal(block br)<mbal(dblock s q)"
        and "bal(dblock s q) = mbal(dblock s q)"
        by(auto simp add: Inv2c_def Inv2c_inner_def)
      thus ?thesis
        by force
    qed
    have p25: "\<forall>d\<in>D. \<not>hasRead s q d p"
    proof auto
      fix d
      assume  d_in_D: "d \<in> D" 
        and hasRead_qdp: "hasRead s q d p"
      have p31: "\<lparr>block=dblock s p, proc=p\<rparr>\<in>blocksRead s q d"
      proof -
        from "d_in_D" p22 
        have hasRead_pdq: "hasRead s p d q" by auto
        with hasRead_qdp phase phase_p inv3
        have "HInv3_R s q p d"
          by(auto simp add: HInv3_def HInv3_inner_def HInv3_L_def)
        with p23 d_in_D
        show ?thesis
          by(auto simp add: HInv3_R_def)
      qed
      from p21 act
      have p32: "bal(dblock s q) < mbal(dblock s p)"
        by(auto simp add: EndPhase1_def)
      with p31 d_in_D hasRead_qdp p24 
      show False
        by(force)
    qed
    with p22
    show ?thesis
      by auto
  next
    case False
    with inv phase
    show ?thesis
      by(auto simp add: HInv5_def HInv5_inner_def HInv5_inner_R_def)
  qed
  then obtain D qq 
    where "D\<in>MajoritySet \<and> (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                   \<and> \<not>hasRead s q d qq)"
    by auto
  moreover
  from act pnq
  have "\<forall>d. hasRead s' q d qq = hasRead s q d qq"
    by(auto simp add: EndPhase1_def InitializePhase_def hasRead_def)
  ultimately show ?thesis
    using disk dblock
    by auto
qed

theorem HEndPhase1_HInv5:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv5 s"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a s"
  and inv2a': "Inv2a s'"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  and inv3: "HInv3 s"
  and inv4: "HInv4 s"
shows "HInv5_inner s' q"
  using HEndPhase1_HInv5_p[OF act inv4 inv2a inv2a' inv2c]
        HEndPhase1_HInv5_q[OF act inv inv1 inv2a' inv2a inv2b inv2c inv3, of q]
  by(auto simp add: HInv5_def HInv5_inner_def HInv5_inner_R_def)

lemma HFail_HInv5_p:
  "HFail s s' p  \<Longrightarrow> HInv5_inner s' p"
  by(auto simp add: Fail_def HInv5_inner_def)

lemma  HFail_blocksOf_q:
  assumes act: "HFail s s' p"
  and pnq: "p\<noteq>q"
  shows "blocksOf s' q \<subseteq> blocksOf s q"
  using assms
  by(auto simp add: Fail_def InitializePhase_def blocksOf_def rdBy_def)

lemma HFail_allBlocks:
  assumes act: "HFail s s' p"
  shows "allBlocks s' \<subseteq> allBlocks s \<union> {dblock s' p}"
proof(auto simp del: HFail_def simp add: allBlocks_def
           dest: HFail_blocksOf_q[OF act])
  fix x pa
  assume x_pa: "x \<in> blocksOf s' pa" and
         x_nblks: "\<forall>xa. x \<notin> blocksOf s xa"
  show "x=dblock s' p"
  proof(cases "p=pa")
    case True
    from x_nblks
    have "x \<notin> blocksOf s p"
      by auto
    with True subsetD[OF HFail_blocksOf[OF act] x_pa]
    show ?thesis
      by auto
  next
    case False
    from x_nblks subsetD[OF HFail_blocksOf_q[OF act False] x_pa]
    show ?thesis
      by auto
  qed
qed

lemma HFail_HInv5_q1:
  assumes act: "HFail s s' p"
  and pnq: "p\<noteq>q"
  and inv2a: "Inv2a_inner s' q"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
proof(auto simp add: maxBalInp_def)
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and bal: "bal (dblock s' q) \<le> bal bk"
  from act pnq
  have dblock': "dblock s' q = dblock s q" by(auto simp add: Fail_def)
  from subsetD[OF HFail_allBlocks[OF act] bk]
  show "inp bk = inp (dblock s' q)"
  proof
    assume bk: "bk \<in> allBlocks s"
    with inv5_1 dblock' bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    with act have bk_init: "bk = InitDB"
      by(auto simp add: Fail_def)
    with bal
    have "bal (dblock s' q)=0"
      by(auto simp add: InitDB_def)
    with inv2a
    have "inp (dblock s' q)= NotAnInput"
      by(auto simp add: Inv2a_inner_def Inv2a_innermost_def blocksOf_def)
    with bk_init
    show ?thesis
      by(auto simp add: InitDB_def)
  qed
qed

lemma HFail_HInv5_q2:
  assumes act: "HFail s s' p"
  and pnq: "p\<noteq>q"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from act pnq
  have  disk: "disk s' = disk s"
    and blocksRead: "\<forall>d. blocksRead s' q d = blocksRead s q d"
    and dblock: "dblock s' q = dblock s q"
    by(auto simp add: Fail_def InitializePhase_def)
  with inv5_2
  show ?thesis
    by(auto simp add: hasRead_def)
qed

lemma HFail_HInv5_q:
  assumes act: "HFail s s' p"
  and inv: "HInv5_inner s q"
  and pnq: "p\<noteq>q"
  and inv2a: "Inv2a s'"
  shows "HInv5_inner s' q"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' q = 2"
    and nR2: " \<forall>D\<in>MajoritySet.
        \<forall>qa. \<exists>d\<in>D. bal (dblock s' q) < mbal (disk s' d qa) \<longrightarrow>
                   hasRead s' q d qa" (is "?P s'")
  from HFail_HInv5_q2[OF act pnq]
  have "\<not> (?P s) \<Longrightarrow> \<not>(?P s')"
    by auto
  with nR2
  have P: "?P s"
    by blast
  from inv2a
  have inv2a': "Inv2a_inner s' q" by (auto simp add: Inv2a_def)
  from act pnq phase'
  have "phase s q = 2" 
    by(auto simp add: Fail_def split: if_split_asm)
  with inv HFail_HInv5_q1[OF act pnq inv2a'] P
  show "maxBalInp s' (bal (dblock s' q)) (inp (dblock s' q))"
    by(auto simp add: HInv5_inner_def HInv5_inner_R_def)
qed

theorem HFail_HInv5:
  "\<lbrakk> HFail s s' p; HInv5_inner s q; Inv2a s' \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
by(blast dest: HFail_HInv5_q HFail_HInv5_p)

lemma HPhase0Read_HInv5_p:
  "HPhase0Read s s' p d \<Longrightarrow> HInv5_inner s' p"
  by(auto simp add: Phase0Read_def HInv5_inner_def)

lemma HPhase0Read_allBlocks:
  assumes act: "HPhase0Read s s' p d"
  shows "allBlocks s' \<subseteq> allBlocks s"
  using HPhase0Read_blocksOf[OF act]
  by(auto simp add: allBlocks_def)

lemma HPhase0Read_HInv5_1:
  assumes act: "HPhase0Read s s' p d"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
  using assms and HPhase0Read_blocksOf[OF act]
  by(auto simp add: Phase0Read_def maxBalInp_def allBlocks_def)

lemma HPhase0Read_HInv5_q2:
  assumes act: "HPhase0Read s s' p d"
  and pnq: "p\<noteq>q"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from act pnq
  have  disk: "disk s' = disk s"
    and blocksRead: "\<forall>d. blocksRead s' q d = blocksRead s q d"
    and dblock: "dblock s' q = dblock s q"
    by(auto simp add: Phase0Read_def InitializePhase_def)
  with inv5_2
  show ?thesis
    by(auto simp add: hasRead_def)
qed

lemma HPhase0Read_HInv5_q:
  assumes act: "HPhase0Read s s' p d"
  and inv: "HInv5_inner s q"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
proof(auto simp add: HInv5_inner_def HInv5_inner_R_def)
  assume phase': "phase s' q = 2"
    and i2: "\<forall>D\<in>MajoritySet. \<forall>qa. \<exists>d\<in>D. bal (dblock s' q) < mbal (disk s' d qa) \<longrightarrow> hasRead s' q d qa"
  from phase' act have phase: "phase s q = 2" 
    by(auto simp add: Phase0Read_def)
  show "maxBalInp s' (bal (dblock s' q)) (inp (dblock s' q))"
  proof(rule HPhase0Read_HInv5_1[OF act, of q])
    from HPhase0Read_HInv5_q2[OF act pnq] inv i2 phase
    show "maxBalInp s (bal (dblock s q)) (inp (dblock s q))"
      by(auto simp add: HInv5_inner_def HInv5_inner_R_def, blast)
  qed
qed

theorem HPhase0Read_HInv5:
  "\<lbrakk> HPhase0Read s s' p d; HInv5_inner s q \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
by(blast dest: HPhase0Read_HInv5_q HPhase0Read_HInv5_p)


lemma HEndPhase0_HInv5_p:
  "HEndPhase0 s s' p  \<Longrightarrow> HInv5_inner s' p"
  by(auto simp add: EndPhase0_def HInv5_inner_def)

lemma  HEndPhase0_blocksOf_q:
  assumes act: "HEndPhase0 s s' p"
  and pnq: "p\<noteq>q"
  shows "blocksOf s' q \<subseteq> blocksOf s q"
proof -
  from act pnq
  have dblock: "{dblock s' q} \<subseteq> {dblock s q}"
    and disk: "disk s' = disk s"
    and blks: "blocksRead s' q = blocksRead s q"
    by(auto simp add: EndPhase0_def InitializePhase_def)
  from disk
  have disk': "{disk s' d q | d . d\<in> UNIV} \<subseteq> {disk s d q | d . d\<in> UNIV}" (is "?D' \<subseteq> ?D") 
    by auto
  from pnq act
  have "(UN qq d. rdBy s' q qq d) \<subseteq> (UN qq d. rdBy s q qq d)" 
    by(auto simp add: EndPhase0_def InitializePhase_def 
                rdBy_def split: if_split_asm, blast)
  hence "{block br | br. br \<in> (UN qq d. rdBy s' q qq d)} \<subseteq> 
         {block br | br. br \<in> (UN qq d. rdBy s q qq d)}" 
    (is "?R' \<subseteq> ?R")
    by auto blast
  from union_inclusion[OF dblock union_inclusion[OF disk' this]]
  show ?thesis
    by(auto simp add: blocksOf_def)  
qed

lemma HEndPhase0_allBlocks:
  assumes act: "HEndPhase0 s s' p"
  shows "allBlocks s' \<subseteq> allBlocks s \<union> {dblock s' p}"
proof(auto simp del: HEndPhase0_def simp add: allBlocks_def
           dest: HEndPhase0_blocksOf_q[OF act])
  fix x pa
  assume x_pa: "x \<in> blocksOf s' pa" and
         x_nblks: "\<forall>xa. x \<notin> blocksOf s xa"
  show "x=dblock s' p"
  proof(cases "p=pa")
    case True
    from x_nblks
    have "x \<notin> blocksOf s p"
      by auto
    with True subsetD[OF HEndPhase0_blocksOf[OF act] x_pa]
    show ?thesis
      by auto
  next
    case False
    from x_nblks subsetD[OF HEndPhase0_blocksOf_q[OF act False] x_pa]
    show ?thesis
      by auto
  qed
qed
   
lemma HEndPhase0_HInv5_q1:
  assumes act: "HEndPhase0 s s' p"
  and pnq: "p\<noteq>q"
  and inv1: "Inv1 s"
  and inv5_1: "maxBalInp s (bal(dblock s q)) (inp(dblock s q))"
  shows "maxBalInp s' (bal(dblock s' q)) (inp(dblock s' q))"
proof(auto simp add: maxBalInp_def)
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and bal: "bal (dblock s' q) \<le> bal bk"
  from act pnq
  have dblock': "dblock s' q = dblock s q" by(auto simp add: EndPhase0_def)
  from subsetD[OF HEndPhase0_allBlocks[OF act] bk]
  show "inp bk = inp (dblock s' q)"
  proof
    assume bk: "bk \<in> allBlocks s"
    with inv5_1 dblock' bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk \<in> {dblock s' p}"
    with HEndPhase0_some[OF act inv1] act
    have "\<exists>ba\<in>allBlocksRead s p. bal ba = bal (dblock s' p) \<and> inp ba = inp (dblock s' p)"
      by(auto simp add: EndPhase0_def)
    then obtain ba 
      where ba_blksread: "ba\<in>allBlocksRead s p" 
      and ba_balinp: "bal ba = bal (dblock s' p) \<and> inp ba = inp (dblock s' p)"
      by auto
    have "allBlocksRead s p \<subseteq> allBlocks s"
      by(auto simp add: allBlocksRead_def allRdBlks_def 
                      allBlocks_def blocksOf_def rdBy_def)
    from subsetD[OF this ba_blksread] ba_balinp bal bk dblock' inv5_1
    show ?thesis
      by(auto simp add: maxBalInp_def)
  qed
qed

lemma HEndPhase0_HInv5_q2:
  assumes act: "HEndPhase0 s s' p"
  and pnq: "p\<noteq>q"
  and inv5_2: "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s q) < mbal(disk s d qq)
                                     \<and> \<not>hasRead s q d qq)"
  shows "\<exists>D\<in>MajoritySet. \<exists>qq. (\<forall>d\<in>D.    bal(dblock s' q) < mbal(disk s' d qq)
                                     \<and> \<not>hasRead s' q d qq)"
proof -
  from act pnq
  have  disk: "disk s' = disk s"
    and blocksRead: "\<forall>d. blocksRead s' q d = blocksRead s q d"
    and dblock: "dblock s' q = dblock s q"
    by(auto simp add: EndPhase0_def InitializePhase_def)
  with inv5_2
  show ?thesis
    by(auto simp add: hasRead_def)
qed

lemma HEndPhase0_HInv5_q:
  assumes act: "HEndPhase0 s s' p"
  and inv: "HInv5_inner s q"
  and inv1: "Inv1 s"
  and pnq: "p\<noteq>q"
  shows "HInv5_inner s' q"
  using assms and
    HEndPhase0_HInv5_q1[OF act pnq inv1] 
    HEndPhase0_HInv5_q2[OF act pnq]
  by(auto simp add: HInv5_inner_def HInv5_inner_R_def EndPhase0_def)

theorem HEndPhase0_HInv5:
  "\<lbrakk> HEndPhase0 s s' p; HInv5_inner s q; Inv1 s \<rbrakk> \<Longrightarrow> HInv5_inner s' q"
  by(blast dest: HEndPhase0_HInv5_q HEndPhase0_HInv5_p)

text\<open>
  $HInv1 \wedge HInv2 \wedge HInv3 \wedge HInv4 \wedge HInv5$ is an invariant of $HNext$.

\<close>

lemma I2e:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s \<and> HInv2 s \<and> HInv2 s' \<and> HInv3 s \<and> HInv4 s \<and> HInv5 s"
  shows "HInv5 s'"
  using assms
  by(auto simp add: HInv5_def HNext_def Next_def,
       auto simp add: HInv2_def intro: HStartBallot_HInv5,
       auto intro: HPhase0Read_HInv5,
        auto simp add: HInv4_def intro: HPhase1or2Write_HInv5,
        auto simp add: Phase1or2Read_def
             intro: HPhase1or2ReadThen_HInv5
                    HPhase1or2ReadElse_HInv5,
        auto simp add: EndPhase1or2_def HInv1_def HInv4_def HInv5_def
             intro: HEndPhase1_HInv5
                    HEndPhase2_HInv5,
        auto intro: HFail_HInv5,
        auto intro: HEndPhase0_HInv5 simp add: HInv1_def)

end



