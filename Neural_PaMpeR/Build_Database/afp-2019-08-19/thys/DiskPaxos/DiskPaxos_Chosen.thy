(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Chosen imports DiskPaxos_Inv5 begin

subsection \<open>Lemma I2f\<close>

text \<open>
  To prove the final conjunct we will use the predicate $valueChosen(v)$.
  This predicate is true if $v$ is the only possible value that can be 
  chosen as output. It also asserts that, for every disk $d$ in $D$, if $q$
  has already read $disk s d p$, then it has read a block with $bal$ field 
  at least $b$.
\<close>

definition valueChosen :: "state \<Rightarrow> InputsOrNi \<Rightarrow> bool"
where
  "valueChosen s v =
  (\<exists>b\<in> (UN p. Ballot p). 
         maxBalInp s b v
      \<and> (\<exists>p. \<exists>D\<in>MajoritySet.(\<forall>d\<in>D.  b \<le> bal(disk s d p)
                                   \<and>(\<forall>q.(   phase s q = 1
                                          \<and> b \<le>mbal(dblock s q)
                                          \<and> hasRead s q d p
                                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br))
                             ))))"

lemma HEndPhase1_valueChosen_inp:
  assumes act: "HEndPhase1 s s' q"
  and inv2a: "Inv2a s"
  and asm1: "b \<in> (UN p. Ballot p)"
  and bk_blocksOf: "bk\<in>blocksOf s r"
  and bk: "bk\<in> blocksSeen s q"
  and b_bal: "b \<le> bal bk"
  and asm3: "maxBalInp s b v"
  and inv1: "Inv1 s"
  shows "inp(dblock s' q) = v"
proof -
  from bk_blocksOf inv2a
  have inv2a_bk: "Inv2a_innermost s r bk"
    by(auto simp add: Inv2a_def Inv2a_inner_def)
  from Ballot_nzero asm1
  have "0 < b " by auto
  with b_bal
  have "0< bal bk" by auto
  with inv2a_bk
  have "inp bk \<noteq> NotAnInput"
    by(auto simp add: Inv2a_innermost_def)
  with bk InputsOrNi
  have bk_noninit: "bk \<in> nonInitBlks s q"
    by(auto simp add: nonInitBlks_def blocksSeen_def 
                      allBlocksRead_def allRdBlks_def)
  with maxBlk_in_nonInitBlks[OF this inv1] b_bal
  have maxBlk_b: "b \<le> bal (maxBlk s q)"
    by auto
  from maxBlk_in_nonInitBlks[OF bk_noninit inv1]
  have "\<exists>p d. maxBlk s q \<in> blocksSeen s p"
    by(auto simp add: nonInitBlks_def blocksSeen_def)
  hence "\<exists>p. maxBlk s q \<in> blocksOf s p"
    by(auto simp add: blocksOf_def blocksSeen_def 
      allBlocksRead_def allRdBlks_def rdBy_def, force)
  with maxBlk_b asm3
  have "inp(maxBlk s q) = v"
    by(auto simp add: maxBalInp_def allBlocks_def)
  with bk_noninit act
  show ?thesis
    by(auto simp add: EndPhase1_def)
qed

lemma HEndPhase1_maxBalInp:
  assumes act: "HEndPhase1 s s' q"
    and asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"

  and inv1: "Inv1 s"
  and inv2a: "Inv2a s"
  and inv2b: "Inv2b s"
  shows "maxBalInp s' b v"
proof(cases "b \<le> mbal(dblock s q)")
  case True
  show ?thesis
  proof(cases "p\<noteq>q")
    assume pnq: "p\<noteq>q"
    have "\<exists>d\<in>D. hasRead s q d p"
    proof -
      from act
      have "IsMajority({d. d\<in> disksWritten s q \<and> (\<forall>r\<in>UNIV-{q}. hasRead s q d r)})" (is "IsMajority(?M)") 
        by(auto simp add: EndPhase1_def)  
      with majorities_intersect asm2
      have "D \<inter> ?M \<noteq> {}"
        by(auto simp add: MajoritySet_def)
      hence "\<exists>d\<in>D. (\<forall>r\<in>UNIV-{q}. hasRead s q d r)"
        by auto
      with pnq
      show ?thesis
        by auto
    qed
    then obtain d where p41: "d\<in>D \<and> hasRead s q d p" by auto
    with asm4 asm3 act True
    have p42: "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
      by(auto simp add: EndPhase1_def)
    from True act
    have thesis_L: "b\<le>bal (dblock s' q)"
      by(auto simp add: EndPhase1_def)
    from p42
    have "inp(dblock s' q) = v"
    proof auto
      fix br
      assume br: "br \<in> blocksRead s q d"
        and b_bal: " b \<le> bal (block br)"
      hence br_rdBy: "br \<in> (UN q d. rdBy s (proc br) q d)"
        by(auto simp add:  rdBy_def)
      hence br_blksof: "block br \<in> blocksOf s (proc br)"
        by(auto simp add: blocksOf_def)
      from br have br_bseen: "block br\<in> blocksSeen s q"
        by(auto simp add: blocksSeen_def allBlocksRead_def allRdBlks_def)
      from HEndPhase1_valueChosen_inp[OF act inv2a asm1 br_blksof br_bseen b_bal asm3 inv1]
      show ?thesis .
    qed
    with asm3 HEndPhase1_allBlocks[OF act]
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    case False
    from asm4
    have p41: "\<forall>d\<in>D. b \<le> bal(disk s d p)"
      by auto
    have p42: "\<exists>d\<in>D. disk s d p = dblock s p"
    proof -
      from act
      have "IsMajority {d. d\<in>disksWritten s q \<and> (\<forall>p\<in>UNIV-{q}. hasRead s q d p)}" (is "IsMajority ?S")
        by(auto simp add: EndPhase1_def)
      with majorities_intersect asm2
      have "D \<inter> ?S \<noteq> {}"
        by(auto simp add: MajoritySet_def)
      hence "\<exists>d\<in>D. d\<in>disksWritten s q"
        by auto
      with inv2b False
      show ?thesis
        by(auto simp add: Inv2b_def Inv2b_inner_def)
    qed
    have "inp(dblock s' q) = v"
    proof -
      from p42 p41 False
      have b_bal: "b \<le> bal(dblock s q)" by auto
      have db_blksof: "(dblock s q) \<in> blocksOf s q"
        by(auto simp add: blocksOf_def)
      have db_bseen: "(dblock s q) \<in> blocksSeen s q"
        by(auto simp add: blocksSeen_def)
      from HEndPhase1_valueChosen_inp[OF act inv2a asm1 db_blksof db_bseen b_bal asm3 inv1]
      show ?thesis .
    qed
    with asm3 HEndPhase1_allBlocks[OF act]
    show ?thesis
      by(auto simp add: maxBalInp_def)
  qed
next
  case False
  have "dblock s' q \<in> allBlocks s'"
    by(auto simp add: allBlocks_def blocksOf_def)
  show ?thesis
  proof(auto simp add: maxBalInp_def)
    fix bk
    assume bk: "bk \<in> allBlocks s'"
      and b_bal: "b \<le> bal bk"
    from subsetD[OF HEndPhase1_allBlocks[OF act] bk]
    show "inp bk = v"
    proof
      assume bk: "bk \<in> allBlocks s"
      with asm3 b_bal 
      show ?thesis
        by(auto simp add: maxBalInp_def)
    next
      assume bk: "bk \<in>  {dblock s' q}"
      from act False
      have " \<not> b \<le> bal (dblock s' q)"
        by(auto simp add: EndPhase1_def)
      with bk b_bal
      show ?thesis
        by(auto)
    qed
  qed
qed

lemma HEndPhase1_valueChosen2:
  assumes act: "HEndPhase1 s s' q"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: EndPhase1_def)
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
  with act
  have p31: "phase s q = 1"
    and p32: "dblock s' q = dblock s q"
    by(auto simp add: EndPhase1_def split: if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover
  assume hasRead: "hasRead s' q d p"
  with act
  have "hasRead s q d p"
    by(auto simp add: EndPhase1_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: EndPhase1_def InitializePhase_def hasRead_def)
qed

theorem HEndPhase1_valueChosen:
  assumes act: "HEndPhase1 s s' q"
  and vc: "valueChosen s v"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a s"
  and inv2b: "Inv2b s"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HEndPhase1_maxBalInp[OF act asm1 asm2 asm3 asm4 inv1 inv2a inv2b]
  have "maxBalInp s' b v" .
  with HEndPhase1_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

lemma HStartBallot_maxBalInp:
  assumes act: "HStartBallot s s' q"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HStartBallot_allBlocks[OF act] bk]
  show "inp bk = v"
  proof
    assume bk: "bk\<in>allBlocks s"
    with asm3 b_bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk\<in>{dblock s' q}"
    from asm3
    have "b\<le> bal(dblock s q) \<Longrightarrow> inp(dblock s q) = v"
      by(auto simp add: maxBalInp_def allBlocks_def blocksOf_def)
    with act bk b_bal
    show ?thesis
      by(auto simp add: StartBallot_def)
  qed
qed

lemma HStartBallot_valueChosen2:
  assumes act: "HStartBallot s s' q"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: StartBallot_def)
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act hasRead
  have p31: "phase s q = 1"
   and p32: "dblock s' q = dblock s q"
    by(auto simp add: StartBallot_def InitializePhase_def
                 hasRead_def split : if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover 
  from act hasRead
  have "hasRead s q d p"
    by(auto simp add: StartBallot_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: StartBallot_def InitializePhase_def
                      hasRead_def)
qed

theorem HStartBallot_valueChosen:
  assumes act: "HStartBallot s s' q"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HStartBallot_maxBalInp[OF act asm3]
  have "maxBalInp s' b v" .
  with HStartBallot_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

lemma HPhase1or2Write_maxBalInp:
  assumes act: "HPhase1or2Write s s' q d"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HPhase1or2Write_allBlocks[OF act] bk] asm3 b_bal
  show "inp bk = v"
    by(auto simp add: maxBalInp_def)
qed

lemma HPhase1or2Write_valueChosen2:
  assumes act: "HPhase1or2Write s s' pp d"
    and asm2: "D\<in>MajoritySet"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
    and inv4: "HInv4a s pp"
  shows "?P s'"
proof(auto)
  fix d1
  assume d: "d1\<in>D"
  show "b \<le> bal (disk s' d1 p)"
  proof(cases "d1=d\<and>pp=p")
    case True
    with inv4 act
    have "HInv4a2 s p"
      by(auto simp add: Phase1or2Write_def HInv4a_def)
    with asm2 majorities_intersect
    have "\<exists>dd\<in>D. bal(disk s dd p)\<le>bal(dblock s p)"
      by(auto simp add: HInv4a2_def MajoritySet_def)
    then obtain dd where p41: "dd\<in>D \<and> bal(disk s dd p)\<le>bal(dblock s p)"
      by auto
    from asm4 p41
    have "b\<le> bal(disk s dd p)"
      by auto
    with p41
    have p42: "b \<le> bal(dblock s p)"
      by auto
    from act True
    have "dblock s p = disk s' d p"
      by(auto simp add: Phase1or2Write_def)
    with p42 True
    show ?thesis
      by auto
  next
    case False
    with act asm4 d
    show ?thesis
      by(auto simp add: Phase1or2Write_def)
  qed
next
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act hasRead
  have p31: "phase s q = 1"
   and p32: "dblock s' q = dblock s q"
    by(auto simp add: Phase1or2Write_def InitializePhase_def
                      hasRead_def split : if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover 
  from act hasRead
  have "hasRead s q d p"
    by(auto simp add: Phase1or2Write_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: Phase1or2Write_def InitializePhase_def
                      hasRead_def)
qed

theorem HPhase1or2Write_valueChosen:
  assumes act: "HPhase1or2Write s s' q d"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  and inv4: "HInv4a s q"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HPhase1or2Write_maxBalInp[OF act asm3]
  have "maxBalInp s' b v" .
  with HPhase1or2Write_valueChosen2[OF act asm2 asm4 inv4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed


lemma HPhase1or2ReadThen_maxBalInp:
  assumes act: "HPhase1or2ReadThen s s' q d p"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HPhase1or2ReadThen_allBlocks[OF act] bk] asm3 b_bal
  show "inp bk = v"
    by(auto simp add: maxBalInp_def)
qed

lemma HPhase1or2ReadThen_valueChosen2:
  assumes act: "HPhase1or2ReadThen s s' q d pp"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix dd
  assume d: "dd\<in>D"
  with act asm4
  show "b \<le> bal (disk s' dd p)"
    by(auto simp add: Phase1or2ReadThen_def)
  fix dd qq
  assume d: "dd\<in>D" 
    and phase': "phase s' qq = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' qq)"
    and hasRead: "hasRead s' qq dd p"
  show "\<exists>br\<in>blocksRead s' qq dd. b \<le> bal (block br)"
  proof(cases "d=dd \<and> qq=q \<and> pp=p")
    case True
    from d asm4
    have "b \<le> bal(disk s dd p)"
      by auto
    with act True
    show ?thesis
      by(auto simp add: Phase1or2ReadThen_def)
  next
    case False
    with phase' act
    have p31: "phase s qq = 1"
      and p32: "dblock s' qq = dblock s qq"
      by(auto simp add: Phase1or2ReadThen_def)
    with dblk_mbal
    have "b\<le>mbal(dblock s qq)" by auto
    moreover 
    from act hasRead False
    have "hasRead s qq dd p"
      by(auto simp add: Phase1or2ReadThen_def 
  hasRead_def split: if_split_asm)
    ultimately
    have "\<exists>br\<in>blocksRead s qq dd. b\<le> bal(block br)"
      using p31 asm4 d
      by blast
    with act hasRead
    show "\<exists>br\<in>blocksRead s' qq dd. b\<le> bal(block br)"
      by(auto simp add: Phase1or2ReadThen_def hasRead_def)
  qed
qed

theorem HPhase1or2ReadThen_valueChosen:
  assumes act: "HPhase1or2ReadThen s s' q d p"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HPhase1or2ReadThen_maxBalInp[OF act asm3]
  have "maxBalInp s' b v" .
  with HPhase1or2ReadThen_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

theorem HPhase1or2ReadElse_valueChosen:
  "\<lbrakk> HPhase1or2ReadElse s s' p d r; valueChosen s v; v\<in> Inputs  \<rbrakk>
     \<Longrightarrow> valueChosen s' v"
  using HStartBallot_valueChosen
  by(auto simp add: Phase1or2ReadElse_def)

lemma HEndPhase2_maxBalInp:
  assumes act: "HEndPhase2 s s' q"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HEndPhase2_allBlocks[OF act] bk] asm3 b_bal
  show "inp bk = v"
    by(auto simp add: maxBalInp_def)
qed

lemma HEndPhase2_valueChosen2:
  assumes act: "HEndPhase2 s s' q"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: EndPhase2_def)
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act hasRead
  have p31: "phase s q = 1"
   and p32: "dblock s' q = dblock s q"
    by(auto simp add: EndPhase2_def InitializePhase_def
                      hasRead_def split : if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover 
  from act hasRead
  have "hasRead s q d p"
    by(auto simp add: EndPhase2_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: EndPhase2_def InitializePhase_def
                      hasRead_def)
qed

theorem HEndPhase2_valueChosen:
  assumes act: "HEndPhase2 s s' q"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HEndPhase2_maxBalInp[OF act asm3]
  have "maxBalInp s' b v" .
  with HEndPhase2_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

lemma HFail_maxBalInp:
  assumes act: "HFail s s' q"
    and asm1: "b \<in> (UN p. Ballot p)"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HFail_allBlocks[OF act] bk]
  show "inp bk = v"
  proof
    assume bk: "bk\<in>allBlocks s"
    with asm3 b_bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk\<in>{dblock s' q}"
    with act
    have "bal bk = 0"
      by(auto simp add: Fail_def InitDB_def)
    moreover
    from Ballot_nzero asm1
    have "0 < b"
      by auto
    ultimately
    show ?thesis
      using b_bal
      by auto
  qed
qed

lemma HFail_valueChosen2:
  assumes act: "HFail s s' q"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: Fail_def)
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act hasRead
  have p31: "phase s q = 1"
   and p32: "dblock s' q = dblock s q"
    by(auto simp add: Fail_def InitializePhase_def
                  hasRead_def split : if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover 
  from act hasRead
  have "hasRead s q d p"
    by(auto simp add: Fail_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: Fail_def InitializePhase_def hasRead_def)
qed

theorem HFail_valueChosen:
  assumes act: "HFail s s' q"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HFail_maxBalInp[OF act asm1 asm3]
  have "maxBalInp s' b v" .
  with HFail_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

lemma HPhase0Read_maxBalInp:
  assumes act: "HPhase0Read s s' q d"
    and asm3: "maxBalInp s b v"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HPhase0Read_allBlocks[OF act] bk] asm3 b_bal
  show "inp bk = v"
    by(auto simp add: maxBalInp_def)
qed

lemma HPhase0Read_valueChosen2:
  assumes act: "HPhase0Read s s' qq dd"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: Phase0Read_def)
next
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act
  have qqnq: "qq\<noteq>q"
    by(auto simp add: Phase0Read_def)
  show "\<exists>br\<in>blocksRead s' q d. b \<le> bal (block br)"
  proof -
    from phase' act hasRead
    have p31: "phase s q = 1"
      and p32: "dblock s' q = dblock s q"
      by(auto simp add: Phase0Read_def hasRead_def)
    with dblk_mbal
    have "b\<le>mbal(dblock s q)" by auto
    moreover 
    from act hasRead qqnq
    have "hasRead s q d p"
      by(auto simp add: Phase0Read_def hasRead_def
                 split: if_split_asm)
    ultimately
    have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
      using p31 asm4 d
      by blast
    with act hasRead
    show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
      by(auto simp add: Phase0Read_def InitializePhase_def
                        hasRead_def)
  qed
qed
  
theorem HPhase0Read_valueChosen:
  assumes act: "HPhase0Read s s' q d"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HPhase0Read_maxBalInp[OF act asm3]
  have "maxBalInp s' b v" .
  with HPhase0Read_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed


lemma HEndPhase0_maxBalInp:
  assumes act: "HEndPhase0 s s' q"
    and asm3: "maxBalInp s b v"
    and inv1: "Inv1 s"
  shows "maxBalInp s' b v"
proof(auto simp add: maxBalInp_def) 
  fix bk
  assume bk: "bk \<in> allBlocks s'"
    and b_bal: "b\<le> bal bk"
  from subsetD[OF HEndPhase0_allBlocks[OF act] bk]
  show "inp bk = v"
  proof
    assume bk: "bk\<in>allBlocks s"
    with asm3 b_bal
    show ?thesis
      by(auto simp add: maxBalInp_def)
  next
    assume bk: "bk\<in>{dblock s' q}"
    with HEndPhase0_some[OF act inv1] act
    have "\<exists>ba\<in>allBlocksRead s q. bal ba = bal (dblock s' q) \<and> inp ba = inp (dblock s' q)"
      by(auto simp add: EndPhase0_def)
    then obtain ba 
      where ba_blksread: "ba\<in>allBlocksRead s q" 
      and ba_balinp: "bal ba = bal (dblock s' q) \<and> inp ba = inp (dblock s' q)"
      by auto
    have "allBlocksRead s q \<subseteq> allBlocks s"
      by(auto simp add: allBlocksRead_def allRdBlks_def
                        allBlocks_def blocksOf_def rdBy_def)
    from subsetD[OF this ba_blksread] ba_balinp bk b_bal asm3
    show ?thesis
      by(auto simp add: maxBalInp_def)
  qed
qed

lemma HEndPhase0_valueChosen2:
  assumes act: "HEndPhase0 s s' q"
    and asm4: "\<forall>d\<in>D.   b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))" (is "?P s")
  shows "?P s'"
proof(auto)
  fix d
  assume d: "d\<in>D"
  with act asm4
  show "b \<le> bal (disk s' d p)"
    by(auto simp add: EndPhase0_def)
  fix d q
  assume d: "d\<in>D"
    and phase': "phase s' q = Suc 0" 
    and dblk_mbal: "b \<le> mbal (dblock s' q)"
    and hasRead: "hasRead s' q d p"
  from phase' act hasRead
  have p31: "phase s q = 1"
   and p32: "dblock s' q = dblock s q"
    by(auto simp add: EndPhase0_def InitializePhase_def
                       hasRead_def split : if_split_asm)
  with dblk_mbal
  have "b\<le>mbal(dblock s q)" by auto
  moreover 
  from act hasRead
  have "hasRead s q d p"
    by(auto simp add: EndPhase0_def InitializePhase_def 
      hasRead_def split: if_split_asm)
  ultimately
  have "\<exists>br\<in>blocksRead s q d. b\<le> bal(block br)"
    using p31 asm4 d
    by blast
  with act hasRead
  show "\<exists>br\<in>blocksRead s' q d. b\<le> bal(block br)"
    by(auto simp add: EndPhase0_def InitializePhase_def
                      hasRead_def)
qed

theorem HEndPhase0_valueChosen:
  assumes act: "HEndPhase0 s s' q"
  and vc: "valueChosen s v"
  and v_input: "v \<in> Inputs"
  and inv1: "Inv1 s"
  shows "valueChosen s' v"
proof -
  from vc
  obtain b p D where
        asm1: "b \<in> (UN p. Ballot p)"
    and asm2: "D\<in>MajoritySet"
    and asm3: "maxBalInp s b v"
    and asm4: "\<forall>d\<in>D.  b \<le> bal(disk s d p)
                   \<and>(\<forall>q.(   phase s q = 1
                          \<and> b \<le>mbal(dblock s q)
                          \<and> hasRead s q d p
                         ) \<longrightarrow> (\<exists>br\<in>blocksRead s q d. b \<le> bal(block br)))"
    by(auto simp add: valueChosen_def)
  from HEndPhase0_maxBalInp[OF act asm3 inv1]
  have "maxBalInp s' b v" .
  with HEndPhase0_valueChosen2[OF act asm4] asm1 asm2
  show ?thesis 
    by(auto simp add: valueChosen_def)
qed

end

