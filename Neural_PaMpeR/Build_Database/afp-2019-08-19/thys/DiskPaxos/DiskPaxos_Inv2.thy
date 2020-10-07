(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Inv2 imports DiskPaxos_Inv1 begin


subsection \<open>Invariant 2\<close>

text \<open>
  The second invariant is split into three main conjuncts called
  $Inv2a$, $Inv2b$, and $Inv2c$. The main difficulty is in proving 
  the preservation of the first conjunct.
\<close>

definition rdBy :: "state \<Rightarrow> Proc \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> BlockProc set"
where
  "rdBy s p q d =
    {br . br \<in> blocksRead s q d \<and> proc br = p}"

definition blocksOf :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock set"
where
  "blocksOf s p =
      {dblock s p}
   \<union> {disk s d p | d . d \<in> UNIV}
   \<union> {block br | br . br \<in> (UN q d. rdBy s p q d) }"

definition allBlocks :: "state \<Rightarrow> DiskBlock set"
  where "allBlocks s = (UN p. blocksOf s p)"

definition Inv2a_innermost :: "state \<Rightarrow> Proc \<Rightarrow> DiskBlock \<Rightarrow> bool"
where
  "Inv2a_innermost s p bk =
    (mbal bk \<in> (Ballot p) \<union> {0}
   \<and> bal bk \<in> (Ballot p) \<union> {0}
   \<and> (bal bk = 0) = (inp bk = NotAnInput)
   \<and> bal bk \<le> mbal bk
   \<and> inp bk \<in> (allInput s) \<union> {NotAnInput})"

definition Inv2a_inner :: "state \<Rightarrow> Proc \<Rightarrow> bool"
  where "Inv2a_inner s p = (\<forall>bk \<in> blocksOf s p. Inv2a_innermost  s p bk)"

definition Inv2a :: "state \<Rightarrow> bool"
  where "Inv2a s = (\<forall>p. Inv2a_inner s p)"

definition Inv2b_inner :: "state \<Rightarrow> Proc \<Rightarrow> Disk \<Rightarrow> bool"
where
  "Inv2b_inner s p d =
     ((d \<in> disksWritten s p \<longrightarrow>
        (phase s p \<in> {1,2} \<and> disk s d p = dblock s p))
   \<and> (phase s p \<in> {1,2} \<longrightarrow>
        (  (blocksRead s p d \<noteq> {} \<longrightarrow> d \<in> disksWritten s p)
         \<and> \<not> hasRead s p d p)))"

definition Inv2b :: "state \<Rightarrow> bool"
  where "Inv2b s = (\<forall>p d. Inv2b_inner s p d)"

definition Inv2c_inner :: "state \<Rightarrow> Proc \<Rightarrow> bool"
where
  "Inv2c_inner s p =
    ((phase s p = 0 \<longrightarrow>
       (  dblock s p = InitDB
        \<and> disksWritten s p = {}
        \<and> (\<forall> d. \<forall> br \<in> blocksRead s p d.
              proc br = p \<and> block br = disk s d p)))
   \<and> (phase s p \<noteq> 0 \<longrightarrow>
        (  mbal(dblock s p) \<in> Ballot p
         \<and> bal(dblock s p) \<in> Ballot p \<union> {0}
         \<and> (\<forall> d. \<forall> br \<in> blocksRead s p d.
               mbal(block br) < mbal(dblock s p))))
   \<and> (phase s p \<in> {2,3} \<longrightarrow> bal(dblock s p) = mbal(dblock s p))
   \<and> outpt s p = (if phase s p = 3 then inp(dblock s p) else NotAnInput)
   \<and> chosen s \<in> allInput s \<union> {NotAnInput}
   \<and> (\<forall>p.   inpt s p \<in> allInput s
          \<and> (chosen s = NotAnInput \<longrightarrow> outpt s p = NotAnInput)))"

definition Inv2c :: "state \<Rightarrow> bool"
  where "Inv2c s = (\<forall>p. Inv2c_inner s p)"

definition HInv2 :: "state \<Rightarrow> bool"
  where "HInv2 s = (Inv2a s \<and> Inv2b s \<and> Inv2c s)"


subsubsection \<open>Proofs of Invariant 2 a\<close>

theorem HInit_Inv2a: "HInit s \<longrightarrow> Inv2a s"
by (auto simp add: HInit_def Init_def Inv2a_def Inv2a_inner_def 
                   Inv2a_innermost_def rdBy_def blocksOf_def 
                   InitDB_def)

text\<open>
  For every action we define a action-$blocksOf$ lemma. We have two cases: either 
the new $blocksOf$ is included in the old $blocksOf$, or the new $blocksOf$ is included 
in the old $blocksOf$ union the new $dblock$. In the former case the assumption $inv$ will 
imply the thesis. In the latter, we just have to prove the innermost predicate for 
the particular case of the new $dblock$. 
This particular case is proved in lemma action-$Inv2a$-$dblock$.  
\<close>

lemma HPhase1or2ReadThen_blocksOf:
  "\<lbrakk> HPhase1or2ReadThen s s' p d q \<rbrakk> \<Longrightarrow> blocksOf s' r \<subseteq> blocksOf s r"
  by(auto simp add: Phase1or2ReadThen_def blocksOf_def rdBy_def)

theorem HPhase1or2ReadThen_Inv2a:
  assumes inv: "Inv2a s"
  and act: "HPhase1or2ReadThen s s' p d q"
  shows "Inv2a s'"
proof (clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix pp bk
  assume bk: "bk \<in> blocksOf s' pp"
  with inv HPhase1or2ReadThen_blocksOf[OF act]
  have "Inv2a_innermost s pp bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  with act
  show "Inv2a_innermost s' pp bk"
    by(auto simp add: Inv2a_innermost_def HNextPart_def)
qed

lemma InitializePhase_rdBy:
  "InitializePhase s s' p \<Longrightarrow> rdBy s' pp qq dd \<subseteq> rdBy s pp qq dd"
by(auto simp add: InitializePhase_def rdBy_def)

lemma HStartBallot_blocksOf:
  "HStartBallot s s' p \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q \<union> {dblock s' q}"
by(auto simp add: StartBallot_def blocksOf_def
         dest: subsetD[OF InitializePhase_rdBy])

lemma HStartBallot_Inv2a_dblock:
  assumes act: "HStartBallot s s' p"
  and inv2a: "Inv2a_innermost s p (dblock s p)"
  shows "Inv2a_innermost s' p (dblock s' p)"
proof -
  from act
  have mbal': "mbal (dblock s' p) \<in> Ballot p"
    by(auto simp add: StartBallot_def)
  from act 
  have bal': "bal (dblock s' p) = bal (dblock s p)"
    by(auto simp add: StartBallot_def)
  with act
  have inp': "inp (dblock s' p) = inp (dblock s p)"
    by(auto simp add: StartBallot_def)
  from act
  have "mbal (dblock s p) \<le> mbal (dblock s' p)"
     by(auto simp add: StartBallot_def)
  with bal' inv2a
  have bal_mbal: "bal (dblock s' p) \<le> mbal (dblock s' p)"
    by(auto simp add: Inv2a_innermost_def)
  from act
  have "allInput s \<subseteq> allInput s'"
    by(auto simp add: HNextPart_def) 
  with mbal' bal' inp' bal_mbal act inv2a 
  show ?thesis
  by(auto simp add: Inv2a_innermost_def)
qed

lemma HStartBallot_Inv2a_dblock_q:
  assumes act: "HStartBallot s s' p"
  and inv2a: "Inv2a_innermost s q (dblock s q)"
  shows "Inv2a_innermost s' q (dblock s' q)"
proof(cases "p=q")
  case True
  with act inv2a
  show ?thesis
    by(blast dest: HStartBallot_Inv2a_dblock)
next
  case False
  with act inv2a
  show ?thesis
    by(clarsimp simp add: StartBallot_def HNextPart_def 
      InitializePhase_def Inv2a_innermost_def)
qed

theorem HStartBallot_Inv2a:
  assumes inv: "Inv2a s"
  and act: "HStartBallot s s' p"
  shows "Inv2a s'"
proof (clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  with inv
  have oldBlks: "bk \<in> blocksOf s q \<longrightarrow> Inv2a_innermost s q bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  from bk HStartBallot_blocksOf[OF act] 
  have "bk \<in> {dblock s' q} \<union> blocksOf s q"
    by blast 
  thus "Inv2a_innermost s' q bk"
  proof
    assume bk_dblock: "bk \<in> {dblock s' q}"
    from inv
    have inv_q_dblock: "Inv2a_innermost s q (dblock s q)"
      by(auto simp add: Inv2a_def Inv2a_inner_def Inv2a_innermost_def blocksOf_def)
    with act inv bk_dblock
    show ?thesis
      by(blast dest: HStartBallot_Inv2a_dblock_q)
  next
    assume bk_in_blocks: "bk \<in> blocksOf s q"
    with oldBlks
    have "Inv2a_innermost s q bk" ..
    with act 
    show ?thesis
      by(auto simp add: StartBallot_def HNextPart_def 
                        InitializePhase_def Inv2a_innermost_def)
  qed
qed

lemma HPhase1or2Write_blocksOf:
  "\<lbrakk> HPhase1or2Write s s' p d \<rbrakk> \<Longrightarrow> blocksOf s' r \<subseteq> blocksOf s r"
  by(auto simp add: Phase1or2Write_def blocksOf_def rdBy_def)

theorem HPhase1or2Write_Inv2a:
  assumes inv: "Inv2a s"
  and     act: "HPhase1or2Write s s' p d"
  shows "Inv2a s'"
proof(clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  from inv bk HPhase1or2Write_blocksOf[OF act] 
  have inp_q_bk: "Inv2a_innermost s q bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  with act
  show "Inv2a_innermost s' q bk"
    by(auto simp add: Inv2a_innermost_def HNextPart_def)
qed

theorem HPhase1or2ReadElse_Inv2a:
  assumes inv: "Inv2a s"
  and act:     "HPhase1or2ReadElse s s' p d q"
  shows "Inv2a s'"
proof -
  from act 
  have "HStartBallot s s' p"
    by(simp add: Phase1or2ReadElse_def)
  with inv
  show ?thesis
    by(auto elim: HStartBallot_Inv2a)
qed

lemma HEndPhase2_blocksOf:
  "\<lbrakk> HEndPhase2 s s' p \<rbrakk> \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q"
  by(auto simp add: EndPhase2_def blocksOf_def 
               dest: subsetD[OF InitializePhase_rdBy])

theorem HEndPhase2_Inv2a:
  assumes inv: "Inv2a s"
  and     act: "HEndPhase2 s s' p"
  shows        "Inv2a s'"
proof(clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  from inv bk HEndPhase2_blocksOf[OF act] 
  have inp_q_bk: "Inv2a_innermost s q bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  with act
  show "Inv2a_innermost s' q bk"
    by(auto simp add: Inv2a_innermost_def HNextPart_def)
qed

lemma HFail_blocksOf:
   "HFail s s' p  \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q \<union> {dblock s' q}"
by(auto simp add: Fail_def blocksOf_def
        dest: subsetD[OF InitializePhase_rdBy])

lemma HFail_Inv2a_dblock_q:
  assumes act: "HFail s s' p"
  and     inv: "Inv2a_innermost s q (dblock s q)"
  shows "Inv2a_innermost s' q (dblock s' q)"
proof(cases "p=q")
  case True
  with act
  have "dblock s' q = InitDB" 
    by (simp add: Fail_def) 
  with True 
  show ?thesis
    by(auto simp add: InitDB_def Inv2a_innermost_def)
next
  case False
  with inv act
  show ?thesis
    by(auto simp add: Fail_def HNextPart_def 
      InitializePhase_def Inv2a_innermost_def)
qed

theorem HFail_Inv2a:
 assumes inv: "Inv2a s"
  and     act: "HFail s s' p"
  shows        "Inv2a s'"
proof(clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  with HFail_blocksOf[OF act] 
  have dblock_blocks: "bk \<in> {dblock s' q} \<union> blocksOf s q"
    by blast
  thus "Inv2a_innermost s' q bk"
  proof
    assume bk_dblock: "bk \<in> {dblock s' q}"
    from inv
    have inv_q_dblock: "Inv2a_innermost s q (dblock s q)"
      by(auto simp add: Inv2a_def Inv2a_inner_def Inv2a_innermost_def blocksOf_def)
    with act bk_dblock
    show ?thesis
      by(blast dest: HFail_Inv2a_dblock_q)
  next
    assume bk_in_blocks: "bk \<in> blocksOf s q"
    with inv
    have "Inv2a_innermost s q bk" 
      by (auto simp add: Inv2a_def Inv2a_inner_def)
    with act 
    show ?thesis
      by(auto simp add: Fail_def HNextPart_def 
        InitializePhase_def Inv2a_innermost_def)
  qed
qed

lemma HPhase0Read_blocksOf:
  "HPhase0Read s s' p d \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q"
  by(auto simp add: Phase0Read_def InitializePhase_def 
                       blocksOf_def rdBy_def)

theorem HPhase0Read_Inv2a:
  assumes inv: "Inv2a s"
  and     act: "HPhase0Read s s' p d"
  shows        "Inv2a s'"
proof(clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  from inv bk HPhase0Read_blocksOf[OF act] 
  have inp_q_bk: "Inv2a_innermost s q bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  with act
  show "Inv2a_innermost s' q bk"
    by(auto simp add: Inv2a_innermost_def HNextPart_def)
qed

lemma HEndPhase0_blocksOf:
  " HEndPhase0 s s' p \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q \<union> {dblock s' q}"
  by(auto simp add: EndPhase0_def blocksOf_def 
                  dest: subsetD[OF InitializePhase_rdBy])


lemma HEndPhase0_blocksRead:
  assumes act: "HEndPhase0 s s' p"
  shows "\<exists>d. blocksRead s p d \<noteq> {}"
proof -
  from act 
  have "IsMajority({d. hasRead s p d p})" by(simp add: EndPhase0_def)
  hence "{d. hasRead s p d p} \<noteq> {}" by (rule majority_nonempty)
  thus ?thesis
    by(auto simp add: hasRead_def)
qed

text \<open>$EndPhase0$ has the additional difficulty of having a choose expression. We
prove that there exists an $x$ such that the predicate of the choose expression holds,
and then apply $someI$: @{thm someI}.
\<close>

lemma HEndPhase0_some:
  assumes act:  "HEndPhase0 s s' p"
  and    inv1:  "Inv1 s"
  shows  "(SOME b.    b \<in> allBlocksRead s p 
                   \<and> (\<forall>t\<in>allBlocksRead s p. bal t \<le> bal b)
          ) \<in> allBlocksRead s p 
        \<and> (\<forall>t\<in>allBlocksRead s p. 
             bal t \<le> bal (SOME b.    b \<in> allBlocksRead s p 
                                  \<and> (\<forall>t\<in>allBlocksRead s p. bal t \<le> bal b)))"
proof -
  from inv1 have "finite (bal ` allBlocksRead s p)" (is "finite ?S")
    by(simp add: Inv1_def allBlocksRead_def)
  moreover
  from HEndPhase0_blocksRead[OF act] 
  have "?S \<noteq> {}"
    by(auto simp add: allBlocksRead_def allRdBlks_def)
  ultimately 
  have "Max ?S \<in> ?S" and "\<forall>t \<in> ?S. t \<le> Max ?S" by auto
  hence "\<exists>r \<in> ?S. \<forall>t \<in> ?S. t \<le> r" ..
  then obtain mblk
    where "   mblk \<in> allBlocksRead s p 
           \<and> (\<forall>t \<in> allBlocksRead s p. bal t \<le> bal mblk)" (is "?P mblk")
    by auto
  thus ?thesis
    by (rule someI)
qed

lemma HEndPhase0_dblock_allBlocksRead:
  assumes act:  "HEndPhase0 s s' p"
  and    inv1:  "Inv1 s"
  shows   "dblock s' p \<in> (\<lambda>x. x \<lparr>mbal:= mbal(dblock s' p)\<rparr>) ` allBlocksRead s p"
using act HEndPhase0_some[OF act inv1]
    by(auto simp add: EndPhase0_def)

lemma HNextPart_allInput_or_NotAnInput:
  assumes act: "HNextPart s s'"
  and inv2a: "Inv2a_innermost s p (dblock s' p)"
  shows "inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
 proof -
   from act
   have "allInput s' = allInput s \<union> (range (inpt s'))"
     by(simp add: HNextPart_def)
   moreover
   from inv2a
   have "inp (dblock s' p) \<in> allInput s \<union> {NotAnInput}"
     by(simp add: Inv2a_innermost_def)
   ultimately show ?thesis
     by blast
qed

lemma HEndPhase0_Inv2a_allBlocksRead:
  assumes act: "HEndPhase0 s s' p"
  and inv2a: "Inv2a_inner s p"
  and inv2c: "Inv2c_inner s p"
  shows "\<forall>t \<in> (\<lambda>x. x \<lparr>mbal:= mbal (dblock s' p)\<rparr>) ` allBlocksRead s p. 
          Inv2a_innermost s p t"
proof -
  from act
  have mbal': "mbal (dblock s' p) \<in> Ballot p"
    by(auto simp add: EndPhase0_def)
  from inv2c act
  have allproc_p: "\<forall>d. \<forall>br \<in> blocksRead s p d. proc br = p"
    by(simp add: Inv2c_inner_def EndPhase0_def)
  with inv2a
  have allBlocks_inv2a: "\<forall>t \<in> allBlocksRead s p. Inv2a_innermost s p t"
  proof(auto simp add: Inv2a_inner_def allBlocksRead_def 
                       allRdBlks_def blocksOf_def rdBy_def)
    fix d bk
    assume bk_in_blocksRead: "bk \<in> blocksRead s p d"
      and inv2a_bk: "\<forall>x\<in>     {u. \<exists>d. u = disk s d p} 
                           \<union> {block br |br. (\<exists>q d. br \<in> blocksRead s q d) 
                         \<and> proc br = p}. Inv2a_innermost s p x"
    with allproc_p have "proc bk = p"  by auto
    with bk_in_blocksRead inv2a_bk
    show "Inv2a_innermost s p (block bk)" by blast
  qed 
  from act
  have mbal'_gt: "\<forall>bk \<in> allBlocksRead s p. mbal bk \<le> mbal (dblock s' p)"
    by(auto simp add: EndPhase0_def)
  with  mbal' allBlocks_inv2a
  show ?thesis
  proof (auto simp add: Inv2a_innermost_def)
    fix t
    assume t_blocksRead: "t \<in> allBlocksRead s p"
    with allBlocks_inv2a
    have "bal t \<le> mbal t" by (auto simp add: Inv2a_innermost_def)
    moreover
    from t_blocksRead mbal'_gt 
    have "mbal t \<le> mbal (dblock s' p)" by blast
    ultimately show "bal t \<le> mbal (dblock s' p)"
      by auto
  qed
qed

lemma HEndPhase0_Inv2a_dblock:
  assumes act: "HEndPhase0 s s' p"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a_inner s p"
  and inv2c: "Inv2c_inner s p"
  shows "Inv2a_innermost s' p (dblock s' p)"
proof -
  from act inv2a inv2c
  have t1: "\<forall>t \<in> (\<lambda>x. x \<lparr>mbal:= mbal (dblock s' p)\<rparr>) ` allBlocksRead s p. 
                  Inv2a_innermost s p t"
    by(blast dest: HEndPhase0_Inv2a_allBlocksRead)
  from act inv1
  have "dblock s' p \<in> (\<lambda>x. x \<lparr>mbal:= mbal(dblock s' p)\<rparr>) ` allBlocksRead s p"
    by(simp, blast dest: HEndPhase0_dblock_allBlocksRead)
  with t1
  have inv2_dblock: "Inv2a_innermost s p (dblock s' p)" by auto 
  with act
  have "inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_allInput_or_NotAnInput)
  with inv2_dblock
  show ?thesis
    by(auto simp add: Inv2a_innermost_def)
qed

lemma HEndPhase0_Inv2a_dblock_q:
  assumes act: "HEndPhase0 s s' p"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a_inner s q"
  and inv2c: "Inv2c_inner s p"
  shows "Inv2a_innermost s' q (dblock s' q)" 
proof(cases "p=q")
  case True
  with act inv2a inv2c inv1
  show ?thesis
    by(blast dest: HEndPhase0_Inv2a_dblock)
next
  case False
  from inv2a
  have inv_q_dblock: "Inv2a_innermost s q (dblock s q)"
    by(auto simp add: Inv2a_inner_def blocksOf_def)
  with False act
  show ?thesis
    by(clarsimp simp add: EndPhase0_def HNextPart_def 
      InitializePhase_def Inv2a_innermost_def) 
qed

theorem HEndPhase0_Inv2a:
  assumes inv: "Inv2a s"
  and     act: "HEndPhase0 s s' p"
  and    inv1: "Inv1 s"
  and   inv2c: "Inv2c_inner s p"
  shows        "Inv2a s'"
proof(clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk: "bk \<in> blocksOf s' q"
  with HEndPhase0_blocksOf[OF act]
  have dblock_blocks: "bk \<in> {dblock s' q} \<union> blocksOf s q"
    by blast
  thus "Inv2a_innermost s' q bk"
  proof
    from inv 
    have inv_q: "Inv2a_inner s q"
      by(auto simp add: Inv2a_def)
    assume "bk \<in> {dblock s' q}"
    with act inv1 inv2c inv_q
    show ?thesis
      by(blast dest:HEndPhase0_Inv2a_dblock_q)
  next
    assume bk_in_blocks: "bk \<in> blocksOf s q"
    with inv
    have "Inv2a_innermost s q bk"
      by(auto simp add: Inv2a_def Inv2a_inner_def)
    with act show ?thesis
      by(auto simp add: EndPhase0_def HNextPart_def
          InitializePhase_def Inv2a_innermost_def)
  qed
qed

lemma HEndPhase1_blocksOf:
  "HEndPhase1 s s' p \<Longrightarrow> blocksOf s' q \<subseteq> blocksOf s q \<union> {dblock s' q}"
by (auto simp add: EndPhase1_def blocksOf_def
         dest: subsetD[OF InitializePhase_rdBy])

lemma maxBlk_in_nonInitBlks:
  assumes b: "b \<in> nonInitBlks s p"
  and inv1: "Inv1 s"
  shows "   maxBlk s p \<in> nonInitBlks s p 
         \<and> (\<forall>c\<in> nonInitBlks s p. bal c \<le> bal (maxBlk s p))"
proof -
  have nibals_finite: "finite (bal ` (nonInitBlks s p))" (is "finite ?S")
  proof (rule finite_imageI)
    from inv1
    have "finite (allRdBlks s p)"
      by (auto simp add: Inv1_def)
    hence "finite (allBlocksRead s p)"
      by (auto simp add: allBlocksRead_def)
    hence "finite (blocksSeen s p)"
      by (simp add: blocksSeen_def)
    thus "finite (nonInitBlks s p)"
      by(auto simp add: nonInitBlks_def intro: finite_subset)
  qed
  from b have "bal ` nonInitBlks s p \<noteq> {}"
    by auto
  with nibals_finite
  have "Max ?S \<in> ?S" and "\<forall>bb \<in> ?S. bb \<le> Max ?S" by auto
  hence "\<exists>mb \<in> ?S. \<forall>bb \<in> ?S. bb \<le> mb" ..
  then obtain mblk
    where "   mblk \<in> nonInitBlks s p 
           \<and> (\<forall>c \<in> nonInitBlks s p. bal c \<le> bal mblk)"
          (is "?P mblk")
    by auto
  hence "?P (SOME b. ?P b)"
    by (rule someI)
  thus ?thesis
    by (simp add: maxBlk_def)
qed

lemma blocksOf_nonInitBlks: 
  "(\<forall>p bk. bk \<in> blocksOf s p \<longrightarrow> P bk) 
       \<Longrightarrow> bk \<in> nonInitBlks s p \<longrightarrow> P bk"
  by(auto simp add: allRdBlks_def blocksOf_def nonInitBlks_def 
                    blocksSeen_def allBlocksRead_def rdBy_def, 
    blast) 

lemma maxBlk_allInput: 
  assumes inv: "Inv2a s" 
  and mblk: "maxBlk s p \<in> nonInitBlks s p"
  shows "inp (maxBlk s p) \<in> allInput s"
proof -
  from inv
  have blocks: "\<forall>p bk. bk \<in> blocksOf s p 
                       \<longrightarrow> inp bk \<in> (allInput s) \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def Inv2a_innermost_def)
  from mblk NotAnInput
  have "inp (maxBlk s p) \<noteq> NotAnInput"
    by(auto simp add: nonInitBlks_def)
  with mblk blocksOf_nonInitBlks[OF blocks]
  show ?thesis
    by auto
qed

lemma HEndPhase1_dblock_allInput: 
  assumes act: "HEndPhase1 s s' p"
  and inv1: "HInv1 s"
  and inv2: "Inv2a s"
  shows inp': "inp (dblock s' p) \<in> allInput s'"
proof -
  from act
  have inpt: "inpt s p \<in> allInput s'"
    by(auto simp add: HNextPart_def EndPhase1_def)
  have "nonInitBlks s p \<noteq> {} \<longrightarrow> inp (maxBlk s p) \<in> allInput s"
  proof
    assume ni: "nonInitBlks s p \<noteq> {}"
    with inv1
    have "maxBlk s p \<in> nonInitBlks s p"
      by (auto simp add: HInv1_def maxBlk_in_nonInitBlks)
    with inv2
    show "inp (maxBlk s p) \<in> allInput s"
      by(blast dest: maxBlk_allInput)
  qed
  with act inpt
  show ?thesis
    by(auto simp add: EndPhase1_def HNextPart_def)
qed

lemma HEndPhase1_Inv2a_dblock:
  assumes act: "HEndPhase1 s s' p"
  and inv1: "HInv1 s"
  and inv2: "Inv2a s"
  and inv2c: "Inv2c_inner s p"
  shows "Inv2a_innermost s' p (dblock s' p)"
proof -
  from inv1 act have inv1': "HInv1 s'" 
    by(blast dest: HEndPhase1_HInv1)
  from inv2
  have inv2a: "Inv2a_innermost s p (dblock s p)"
    by(auto simp add: Inv2a_def Inv2a_inner_def blocksOf_def)
  from act inv2c 
  have mbal': "mbal (dblock s' p) \<in> Ballot p"
    by (auto simp add: EndPhase1_def Inv2c_def Inv2c_inner_def)
  moreover
  from act 
  have bal': "bal (dblock s' p) = mbal (dblock s p)"
    by (auto simp add: EndPhase1_def)
  moreover
  from act inv1 inv2
  have inp': "inp (dblock s' p) \<in> allInput s'"
    by(blast dest: HEndPhase1_dblock_allInput)
  moreover
  with inv1' NotAnInput
  have "inp (dblock s' p) \<noteq> NotAnInput"
    by(auto simp add: HInv1_def)
  ultimately show ?thesis
    using act inv2a
    by(auto simp add: Inv2a_innermost_def EndPhase1_def)
qed

lemma HEndPhase1_Inv2a_dblock_q:
  assumes act: "HEndPhase1 s s' p"
  and inv1: "HInv1 s"
  and inv: "Inv2a s"
  and inv2c: "Inv2c_inner s p"
  shows "Inv2a_innermost s' q (dblock s' q)" 
proof(cases "p=q")
  case True
  with act inv inv2c inv1
  show ?thesis
    by(blast dest: HEndPhase1_Inv2a_dblock)
next
  case False
  from inv
  have inv_q_dblock: "Inv2a_innermost s q (dblock s q)"
    by(auto simp add: Inv2a_def Inv2a_inner_def blocksOf_def)
  with False act
  show ?thesis
    by(clarsimp simp add: EndPhase1_def HNextPart_def 
      InitializePhase_def Inv2a_innermost_def) 
qed

theorem HEndPhase1_Inv2a:
  assumes act: "HEndPhase1 s s' p"
  and inv1: "HInv1 s"
  and inv: "Inv2a s"
  and inv2c: "Inv2c_inner s p"
  shows "Inv2a s'"
proof (clarsimp simp add: Inv2a_def Inv2a_inner_def)
  fix q bk
  assume bk_in_bks: "bk \<in> blocksOf s' q"
  with HEndPhase1_blocksOf[OF act]
  have dblock_blocks: "bk \<in> {dblock s' q} \<union> blocksOf s q"
    by blast
  thus "Inv2a_innermost s' q bk"
  proof
    assume "bk \<in> {dblock s' q}"
    with act inv1 inv2c inv
    show ?thesis
      by(blast dest: HEndPhase1_Inv2a_dblock_q)
  next
    assume bk_in_blocks: "bk \<in> blocksOf s q"
    with inv
    have "Inv2a_innermost s q bk"
      by(auto simp add: Inv2a_def Inv2a_inner_def)
    with act show ?thesis
      by(auto simp add: EndPhase1_def HNextPart_def
          InitializePhase_def Inv2a_innermost_def)
  qed
qed


subsubsection \<open>Proofs of Invariant 2 b\<close>

text\<open>
Invariant 2b is proved automatically, given that 
we expand the definitions involved.
\<close>

theorem HInit_Inv2b: "HInit s \<longrightarrow> Inv2b s"
by (auto simp add: HInit_def Init_def Inv2b_def 
                   Inv2b_inner_def InitDB_def)

theorem HPhase1or2ReadThen_Inv2b:
  "\<lbrakk> Inv2b s; HPhase1or2ReadThen s s' p d q \<rbrakk>
   \<Longrightarrow> Inv2b s'"
by (auto simp add: Phase1or2ReadThen_def Inv2b_def
                   Inv2b_inner_def hasRead_def)

theorem HStartBallot_Inv2b:
  "\<lbrakk> Inv2b s; HStartBallot s s' p \<rbrakk>
   \<Longrightarrow> Inv2b s'"
  by(auto simp add:StartBallot_def InitializePhase_def
                   Inv2b_def Inv2b_inner_def hasRead_def)

theorem HPhase1or2Write_Inv2b:
  "\<lbrakk> Inv2b s; HPhase1or2Write s s' p d \<rbrakk>
   \<Longrightarrow> Inv2b s'"
  by(auto simp add: Phase1or2Write_def Inv2b_def
                    Inv2b_inner_def hasRead_def)

theorem HPhase1or2ReadElse_Inv2b:
  "\<lbrakk> Inv2b s; HPhase1or2ReadElse s s' p d q \<rbrakk>
   \<Longrightarrow> Inv2b s'"
by (auto simp add: Phase1or2ReadElse_def StartBallot_def hasRead_def
                   InitializePhase_def Inv2b_def Inv2b_inner_def)

theorem HEndPhase1_Inv2b:
  "\<lbrakk> Inv2b s; HEndPhase1 s s' p \<rbrakk> \<Longrightarrow> Inv2b s'"
by (auto simp add: EndPhase1_def InitializePhase_def 
                   Inv2b_def Inv2b_inner_def hasRead_def)

theorem HFail_Inv2b:
  "\<lbrakk> Inv2b s; HFail s s' p \<rbrakk>
   \<Longrightarrow> Inv2b s'"
by (auto simp add: Fail_def InitializePhase_def
                   Inv2b_def Inv2b_inner_def hasRead_def)

theorem HEndPhase2_Inv2b:
  "\<lbrakk> Inv2b s; HEndPhase2 s s' p \<rbrakk> \<Longrightarrow> Inv2b s'"
by (auto simp add: EndPhase2_def InitializePhase_def 
                   Inv2b_def Inv2b_inner_def hasRead_def)

theorem HPhase0Read_Inv2b:
  "\<lbrakk> Inv2b s; HPhase0Read s s' p d \<rbrakk> \<Longrightarrow> Inv2b s'"
by (auto simp add: Phase0Read_def Inv2b_def 
                   Inv2b_inner_def hasRead_def)

theorem HEndPhase0_Inv2b:
  "\<lbrakk> Inv2b s; HEndPhase0 s s' p \<rbrakk> \<Longrightarrow> Inv2b s'"
by (auto simp add: EndPhase0_def InitializePhase_def 
                   Inv2b_def Inv2b_inner_def hasRead_def)

subsubsection \<open>Proofs of Invariant 2 c\<close>

theorem HInit_Inv2c: "HInit s \<longrightarrow> Inv2c s"
by (auto simp add: HInit_def Init_def Inv2c_def Inv2c_inner_def)


lemma HNextPart_Inv2c_chosen:
  assumes  hnp: "HNextPart s s'"
  and    inv2c: "Inv2c s"
  and   outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                      then inp(dblock s' p) 
                                      else NotAnInput)"
  and inp_dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
  shows  "chosen s' \<in> allInput s' \<union> {NotAnInput}"
using hnp outpt' inp_dblk inv2c
proof(auto simp add: HNextPart_def Inv2c_def Inv2c_inner_def
           split: if_split_asm)
qed

lemma HNextPart_chosen:
  assumes hnp: "HNextPart s s'"
  shows  "chosen s' = NotAnInput \<longrightarrow> (\<forall>p. outpt s' p = NotAnInput)"
using hnp
proof(auto simp add: HNextPart_def split: if_split_asm)
  fix p pa
  assume o1: "outpt s' p \<noteq> NotAnInput"
  and    o2: "outpt s' (SOME p. outpt s' p \<noteq> NotAnInput) = NotAnInput"
  from o1
  have "\<exists>p. outpt s' p \<noteq> NotAnInput"
    by auto
  hence "outpt s' (SOME p. outpt s' p \<noteq> NotAnInput) \<noteq> NotAnInput"
    by(rule someI_ex)
  with o2
  show "outpt s' pa = NotAnInput"
   by simp
qed

lemma HNextPart_allInput:
  "\<lbrakk> HNextPart s s'; Inv2c s \<rbrakk> \<Longrightarrow> \<forall>p. inpt s' p \<in> allInput s'"
    by(auto simp add: HNextPart_def Inv2c_def Inv2c_inner_def)

theorem HPhase1or2ReadThen_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HPhase1or2ReadThen s s' p d q"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HPhase1or2ReadThen_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: Phase1or2ReadThen_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have "\<forall>p.   inpt s' p \<in> allInput s' 
            \<and> (chosen s' = NotAnInput \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with outpt' chosen' act inv
  show ?thesis
    by(auto simp add: Phase1or2ReadThen_def Inv2c_def Inv2c_inner_def)
qed

theorem HStartBallot_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HStartBallot s s' p"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from act
  have phase': "phase s' p = 1"
    by(simp add: StartBallot_def)
  from act
  have phase: "phase s p \<in> {1,2}"
    by(simp add: StartBallot_def)
  from act inv
  have mbal': "mbal(dblock s' p) \<in> Ballot p"
    by(auto simp add: StartBallot_def Inv2c_def Inv2c_inner_def)
  from inv phase
  have "bal(dblock s p) \<in> Ballot p \<union> {0}"
    by(auto simp add: Inv2c_def Inv2c_inner_def)
  with act
  have bal': "bal(dblock s' p) \<in> Ballot p \<union> {0}"
    by(auto simp add: StartBallot_def)
  from act inv phase phase'
  have blks': "(\<forall>d. \<forall>br \<in> blocksRead s' p d. 
                     mbal(block br) < mbal(dblock s' p))"
    by(auto simp add: StartBallot_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HStartBallot_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: StartBallot_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p.   inpt s' p \<in> allInput s' 
                    \<and> (chosen s' = NotAnInput 
                              \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with phase' mbal' bal' outpt' chosen' act inv blks'
  show ?thesis
  by(auto simp add: StartBallot_def InitializePhase_def 
                    Inv2c_def Inv2c_inner_def)
qed

theorem HPhase1or2Write_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HPhase1or2Write s s' p d"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HPhase1or2Write_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: Phase1or2Write_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p. inpt s' p \<in> allInput s' \<and> (chosen s' = NotAnInput 
                     \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with outpt' chosen' act inv
  show ?thesis
    by(auto simp add: Phase1or2Write_def Inv2c_def Inv2c_inner_def)
qed

theorem HPhase1or2ReadElse_Inv2c:
  " \<lbrakk> Inv2c s; HPhase1or2ReadElse s s' p d q; Inv2a s \<rbrakk> \<Longrightarrow> Inv2c s'"
  by(auto simp add: Phase1or2ReadElse_def dest: HStartBallot_Inv2c)

theorem HEndPhase1_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HEndPhase1 s s' p"
  and inv2a: "Inv2a s"
  and inv1: "HInv1 s"
  shows "Inv2c s'"
proof -
  from inv
  have "Inv2c_inner s p" by (auto simp add: Inv2c_def)
  with inv2a act inv1
  have inv2a': "Inv2a s'"
    by(blast dest: HEndPhase1_Inv2a)
  from act inv
  have mbal': "mbal(dblock s' p) \<in> Ballot p"
    by(auto simp add: EndPhase1_def Inv2c_def Inv2c_inner_def)
  from act
  have bal': "bal(dblock s' p) = mbal (dblock s' p)"
    by(auto simp add: EndPhase1_def)
  from act inv
  have blks': "(\<forall>d. \<forall>br \<in> blocksRead s' p d. 
                        mbal(block br) < mbal(dblock s' p))"
    by(auto simp add: EndPhase1_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: EndPhase1_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p.    inpt s' p \<in> allInput s' 
                    \<and> (chosen s' = NotAnInput 
                            \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with mbal' bal' blks' outpt' chosen' act inv
  show ?thesis
    by(auto simp add: EndPhase1_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
qed

theorem HEndPhase2_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HEndPhase2 s s' p"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HEndPhase2_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: EndPhase2_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p.    inpt s' p \<in> allInput s' 
                    \<and> (chosen s' = NotAnInput
                            \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with outpt' chosen' act inv
  show ?thesis
    by(auto simp add: EndPhase2_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
qed

theorem HFail_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HFail s s' p"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HFail_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: Fail_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p. inpt s' p \<in> allInput s' \<and> (chosen s' = NotAnInput 
                     \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with outpt' chosen' act inv
  show ?thesis
    by(auto simp add: Fail_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
qed

theorem HPhase0Read_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HPhase0Read s s' p d"
  and inv2a: "Inv2a s"
  shows "Inv2c s'"
proof -
  from inv2a act
  have inv2a': "Inv2a s'"
    by(blast dest: HPhase0Read_Inv2a)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: Phase0Read_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p.   inpt s' p \<in> allInput s' 
                    \<and> (chosen s' = NotAnInput 
                             \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput)
  with outpt' chosen' act inv
  show ?thesis
    by(auto simp add: Phase0Read_def 
                      Inv2c_def Inv2c_inner_def)
qed

theorem HEndPhase0_Inv2c:
  assumes inv: "Inv2c s"
  and act: "HEndPhase0 s s' p"
  and inv2a: "Inv2a s"
  and inv1: "Inv1 s"
  shows "Inv2c s'"
proof -
  from inv
  have "Inv2c_inner s p" by (auto simp add: Inv2c_def)
  with inv2a act inv1
  have inv2a': "Inv2a s'"
    by(blast dest: HEndPhase0_Inv2a)
  hence bal': "bal(dblock s' p) \<in> Ballot p \<union> {0}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  from act inv
  have mbal': "mbal(dblock s' p) \<in> Ballot p"
    by(auto simp add: EndPhase0_def Inv2c_def Inv2c_inner_def)
  from act inv
  have blks': "(\<forall>d. \<forall>br \<in> blocksRead s' p d. 
                         mbal(block br) < mbal(dblock s' p))"
    by(auto simp add: EndPhase0_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
  from act inv
  have outpt': "\<forall>p. outpt s' p = (if phase s' p = 3 
                                     then inp(dblock s' p) 
                                     else NotAnInput)"
    by(auto simp add: EndPhase0_def Inv2c_def Inv2c_inner_def)
  from inv2a'
  have dblk: "\<forall>p. inp (dblock s' p) \<in> allInput s' \<union> {NotAnInput}"
    by(auto simp add: Inv2a_def Inv2a_inner_def 
                      Inv2a_innermost_def blocksOf_def)
  with act inv outpt'
  have chosen': "chosen s' \<in> allInput s' \<union> {NotAnInput}"
    by(auto dest: HNextPart_Inv2c_chosen)
  from act inv
  have allinp: "\<forall>p. inpt s' p \<in> allInput s' \<and> (chosen s' = NotAnInput 
                     \<longrightarrow> outpt s' p = NotAnInput)" 
    by(auto dest: HNextPart_chosen HNextPart_allInput )
  with mbal' bal' blks' outpt' chosen' act inv 
  show ?thesis
    by(auto simp add: EndPhase0_def InitializePhase_def 
                      Inv2c_def Inv2c_inner_def)
qed

theorem HInit_HInv2:
  "HInit s \<Longrightarrow> HInv2 s"
using HInit_Inv2a HInit_Inv2b HInit_Inv2c
by(auto simp add: HInv2_def)

text\<open>$HInv1 \wedge HInv2$ is an invariant of $HNext$.\<close> 

lemma I2b:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s \<and> HInv2 s"
  shows "HInv2 s'"
proof(auto simp add: HInv2_def)
  show "Inv2a s'" using assms
    by  (auto simp add: HInv2_def HNext_def Next_def,
         auto intro: HStartBallot_Inv2a,
         auto intro: HPhase1or2Write_Inv2a,
         auto simp add: Phase1or2Read_def
              intro: HPhase1or2ReadThen_Inv2a
                     HPhase1or2ReadElse_Inv2a,
         auto intro: HPhase0Read_Inv2a,
         auto simp add: EndPhase1or2_def Inv2c_def
              intro: HEndPhase1_Inv2a
                     HEndPhase2_Inv2a,
         auto intro: HFail_Inv2a,
         auto simp add: HInv1_def
              intro: HEndPhase0_Inv2a)
  show "Inv2b s'" using assms
    by(auto simp add: HInv2_def HNext_def Next_def,
       auto intro: HStartBallot_Inv2b,
       auto intro: HPhase0Read_Inv2b,
       auto intro: HPhase1or2Write_Inv2b,
       auto simp add: Phase1or2Read_def
            intro: HPhase1or2ReadThen_Inv2b
                   HPhase1or2ReadElse_Inv2b,
       auto simp add: EndPhase1or2_def
            intro: HEndPhase1_Inv2b HEndPhase2_Inv2b,
       auto intro:  HFail_Inv2b HEndPhase0_Inv2b)
  show "Inv2c s'" using assms
    by(auto simp add: HInv2_def HNext_def Next_def,
       auto intro: HStartBallot_Inv2c,
       auto intro: HPhase0Read_Inv2c,
       auto intro: HPhase1or2Write_Inv2c,
       auto simp add: Phase1or2Read_def
            intro: HPhase1or2ReadThen_Inv2c
                   HPhase1or2ReadElse_Inv2c,
       auto simp add: EndPhase1or2_def
            intro: HEndPhase1_Inv2c
                   HEndPhase2_Inv2c,
       auto intro: HFail_Inv2c,
       auto simp add: HInv1_def intro: HEndPhase0_Inv2c)
qed

end
