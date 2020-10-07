(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos_Inv6 imports DiskPaxos_Chosen  begin

subsection \<open>Invariant 6\<close>

text\<open>
The final conjunct of $HInv$ asserts that, once an output has been chosen, 
$valueChosen(chosen)$ holds, and each processor's output equals either $chosen$ or
$NotAnInput$.
\<close>

definition HInv6 :: "state \<Rightarrow> bool"
where
  "HInv6 s = ((chosen s \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s))
              \<and> (\<forall>p. outpt s p \<in> {chosen s, NotAnInput}))"

theorem HInit_HInv6: "HInit s \<Longrightarrow> HInv6 s"
  by(auto simp add: HInit_def Init_def InitDB_def HInv6_def)

lemma HEndPhase2_Inv6_1:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv6 s"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  and inv3: "HInv3 s"
  and inv5: "HInv5_inner s p"
  and chosen': "chosen s' \<noteq> NotAnInput"
  shows "valueChosen s' (chosen s')"
proof(cases "chosen s=NotAnInput")
  from inv5 act
  have inv5R: "HInv5_inner_R s p"
    and phase: "phase s p = 2"
    and ep2_maj: "IsMajority {d .    d \<in> disksWritten s p
                                  \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)}"
    by(auto simp add: EndPhase2_def HInv5_inner_def)
  case True
  have p32: "maxBalInp s (bal(dblock s p)) (inp(dblock s p))"
  proof- 
    have "\<not>(\<exists>D \<in> MajoritySet.\<exists>q. (\<forall>d\<in>D. bal (dblock s p) < mbal (disk s d q) \<and> \<not> hasRead s p d q))"
    proof auto
      fix D q
      assume Dmaj: "D\<in>MajoritySet"
      from ep2_maj Dmaj majorities_intersect
      have "\<exists>d\<in>D. d \<in> disksWritten s p
        \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)"
        by(auto simp add: MajoritySet_def, blast)
      then obtain d 
        where dinD: "d\<in>D" 
        and ddisk: "d \<in> disksWritten s p"
        and dhasR: "\<forall>q \<in> UNIV - {p}. hasRead s p d q"
        by auto
      from inv2b
      have "Inv2b_inner s p d"
        by(auto simp add: Inv2b_def)
      with ddisk
      have "disk s d p = dblock s p"
        by(auto simp add: Inv2b_inner_def)
      with inv2c phase
      have "bal (dblock s p) = mbal(disk s d p)"
        by(auto simp add: Inv2c_def Inv2c_inner_def)
      with dhasR dinD
      show "\<exists>d\<in>D. bal (dblock s p) < mbal (disk s d q) \<longrightarrow> hasRead s p d q"
        by auto
    qed
    with inv5R
    show ?thesis
      by(auto simp add: HInv5_inner_R_def)
  qed
  have p33: "maxBalInp s' (bal(dblock s' p)) (chosen s')"
  proof -
    from act 
    have outpt': "outpt s' = (outpt s) (p:= inp (dblock s p))"
      by(auto simp add: EndPhase2_def)
    have outpt'_q: "\<forall>q. p\<noteq>q \<longrightarrow> outpt s' q = NotAnInput"
    proof auto
      fix q
      assume pnq: "p\<noteq>q"
      from outpt' pnq
      have "outpt s' q= outpt s q"
        by(auto simp add: EndPhase2_def)
      with True inv2c
      show "outpt s' q= NotAnInput"
        by(auto simp add: Inv2c_def Inv2c_inner_def)
    qed
    from True act chosen'
    have "chosen s' = inp (dblock s p)"
    proof(auto simp add: HNextPart_def split: if_split_asm)
      fix pa
      assume outpt'_pa: "outpt s' pa \<noteq> NotAnInput"
      from outpt'_q
      have someeq2: "\<And>pa. outpt s' pa \<noteq> NotAnInput \<Longrightarrow> pa=p"
        by auto
      with outpt'_pa
      have "outpt s' p \<noteq> NotAnInput"
        by auto
      from some_equality[of "\<lambda>p. outpt s' p \<noteq> NotAnInput", OF this someeq2]
      have "(SOME p. outpt s' p \<noteq> NotAnInput) = p" .
      with outpt'
      show  "outpt s' (SOME p. outpt s' p \<noteq> NotAnInput) = inp (dblock s p)"
        by auto
    qed
    moreover
    from act
    have"bal(dblock s' p) = bal(dblock s p)"
      by(auto simp add: EndPhase2_def)
    ultimately
    have "maxBalInp s (bal(dblock s' p)) (chosen s')"
      using p32
      by auto
    with HEndPhase2_allBlocks[OF act]
    show ?thesis
      by(auto simp add: maxBalInp_def)
  qed
  from ep2_maj inv2b majorities_intersect
  have "\<exists>D\<in>MajoritySet. (\<forall>d\<in>D.   disk s d p = dblock s p
                              \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q))"
    by(auto simp add: Inv2b_def Inv2b_inner_def MajoritySet_def)
  then obtain D 
    where Dmaj: "D\<in>MajoritySet" 
    and p34: "\<forall>d\<in>D.   disk s d p = dblock s p
    \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)"
    by auto
  have p35: "\<forall>q. \<forall>d\<in>D. ( phase s q=1 \<and> bal(dblock s p)\<le>mbal(dblock s q)\<and> hasRead s q d p) 
                        \<longrightarrow> \<lparr>block=dblock s p, proc=p\<rparr>\<in>blocksRead s q d"
  proof auto
    fix q d
    assume dD: "d\<in>D" and phase_q: "phase s q= Suc 0" 
      and bal_mbal: "bal(dblock s p)\<le>mbal(dblock s q)" and hasRead: "hasRead s q d p"
    from phase inv2c
    have "bal(dblock s p)=mbal(dblock s p)"
      by(auto simp add: Inv2c_def Inv2c_inner_def)
    moreover
    from inv2c phase
    have "\<forall>br\<in>blocksRead s p d. mbal(block br) < mbal(dblock s p)"
      by(auto simp add: Inv2c_def Inv2c_inner_def)
    ultimately
    have p41: "\<lparr>block=dblock s q, proc=q\<rparr>\<notin>blocksRead s p d"
      using bal_mbal
      by auto
    from phase phase_q
    have "p\<noteq>q" by auto
    with p34 dD
    have "hasRead s p d q"
      by auto
    with phase phase_q hasRead inv3 p41
    show "\<lparr>block = dblock s p, proc = p\<rparr> \<in> blocksRead s q d"
      by(auto simp add: HInv3_def HInv3_inner_def 
                        HInv3_L_def HInv3_R_def)
  qed
  have p36: "\<forall>q. \<forall>d\<in>D. phase s' q=1 \<and> bal(dblock s p) \<le> mbal(dblock s' q) \<and> hasRead s' q d p
                        \<longrightarrow> (\<exists>br\<in>blocksRead s' q d. bal(block br) = bal(dblock s p))"
  proof(auto)
    fix q d
    assume dD: "d \<in> D" and phase_q: "phase s' q = Suc 0" 
           and bal: "bal (dblock s p) \<le> mbal (dblock s' q)"
           and hasRead: "hasRead s' q d p"
    from phase_q act
    have "phase s' q=phase s q \<and> dblock s' q=dblock s q \<and> hasRead s' q d p=hasRead s q d p \<and> blocksRead s' q d=blocksRead s q d"
      by(auto simp add: EndPhase2_def hasRead_def InitializePhase_def)
    with p35 phase_q bal hasRead dD
    have "\<lparr>block=dblock s p, proc=p\<rparr>\<in>blocksRead s' q d"
      by auto
    thus "\<exists>br\<in>blocksRead s' q d. bal(block br) = bal(dblock s p)"
      by force
  qed
  hence p36_2: "\<forall>q. \<forall>d\<in>D. phase s' q=1 \<and> bal(dblock s p) \<le> mbal(dblock s' q) \<and> hasRead s' q d p
                         \<longrightarrow> (\<exists>br\<in>blocksRead s' q d. bal(dblock s p) \<le> bal(block br))"
    by force
  from act 
  have bal_dblock: "bal(dblock s' p)=bal(dblock s p)"
    and disk: "disk s'= disk s"
    by(auto simp add: EndPhase2_def)
  from bal_dblock p33
  have "maxBalInp s' (bal(dblock s p)) (chosen s')"
    by auto
  moreover
  from disk p34
  have  "\<forall>d\<in>D. bal(dblock s p) \<le> bal(disk s' d p) "
    by auto
  ultimately
  have "maxBalInp s' (bal(dblock s p)) (chosen s') \<and>
           (\<exists>D\<in>MajoritySet.
                   \<forall>d\<in>D. bal(dblock s p) \<le> bal (disk s' d p) \<and>
                         (\<forall>q. phase s' q = Suc 0 \<and>
                              bal(dblock s p) \<le> mbal (dblock s' q) \<and> hasRead s' q d p \<longrightarrow>
                              (\<exists>br\<in>blocksRead s' q d. bal(dblock s p) \<le> bal (block br))))"
    using p36_2 Dmaj
    by auto
  moreover
  from phase inv2c
  have "bal(dblock s p)\<in> Ballot p"
    by(auto simp add: Inv2c_def Inv2c_inner_def)
  ultimately
  show ?thesis
    by(auto simp add: valueChosen_def)
next
  case False
  with act
  have p31: "chosen s' = chosen s"
    by(auto simp add: HNextPart_def)
  from False inv
  have "valueChosen s (chosen s)"
    by(auto simp add: HInv6_def)
  from HEndPhase2_valueChosen[OF act this] p31 False InputsOrNi
  show ?thesis
    by auto
qed

lemma valueChosen_equal_case:
  assumes max_v: "maxBalInp s b v"
  and Dmaj: "D \<in> MajoritySet"
  and asm_v: "\<forall>d\<in>D. b \<le> bal (disk s d p)"
  and max_w: "maxBalInp s ba w"
  and Damaj: "Da \<in> MajoritySet"
  and asm_w: "\<forall>d\<in>Da. ba \<le> bal (disk s d pa)"
  and b_ba: "b\<le>ba"
  shows "v=w"
proof -
  have "\<forall>d. disk s d pa \<in> allBlocks s"
    by(auto simp add: allBlocks_def blocksOf_def)
  with majorities_intersect Dmaj Damaj
  have "\<exists>d\<in>D\<inter>Da. disk s d pa \<in> allBlocks s"
    by(auto simp add: MajoritySet_def, blast)
  then obtain d 
    where dinmaj: "d\<in>D\<inter>Da" and dab: "disk s d pa \<in> allBlocks s"
    by auto
  with asm_w 
  have ba: "ba \<le> bal (disk s d pa)"
    by auto
  with b_ba 
  have "b \<le> bal (disk s d pa)"  
    by auto
  with max_v dab
  have v_value: "inp (disk s d pa) = v"
    by(auto simp add: maxBalInp_def)
  from ba max_w dab
  have w_value: "inp (disk s d pa) = w"
    by(auto simp add: maxBalInp_def)
  with v_value
  show ?thesis by auto
qed

lemma valueChosen_equal:
  assumes v: "valueChosen s v"
  and w: "valueChosen s w"
  shows "v=w" using assms
proof (auto simp add: valueChosen_def)
  fix a b aa ba p D pa Da
  assume max_v: "maxBalInp s b v"
    and Dmaj: "D \<in> MajoritySet"
    and asm_v: "\<forall>d\<in>D. b \<le> bal (disk s d p) \<and>
              (\<forall>q. phase s q = Suc 0 \<and>
                   b \<le> mbal (dblock s q) \<and> hasRead s q d p \<longrightarrow>
                   (\<exists>br\<in>blocksRead s q d. b \<le> bal (block br)))"
    and max_w: "maxBalInp s ba w"
    and Damaj: "Da \<in> MajoritySet"
    and asm_w: "\<forall>d\<in>Da. ba \<le> bal (disk s d pa) \<and>
              (\<forall>q. phase s q = Suc 0 \<and>
                   ba \<le> mbal (dblock s q) \<and> hasRead s q d pa \<longrightarrow>
                   (\<exists>br\<in>blocksRead s q d. ba \<le> bal (block br)))"
  from asm_v
  have asm_v: "\<forall>d\<in>D. b \<le> bal (disk s d p)" by auto
  from asm_w
  have asm_w: "\<forall>d\<in>Da. ba \<le> bal (disk s d pa)" by auto
  show "v=w"
  proof(cases "b\<le>ba")
    case True
    from valueChosen_equal_case[OF max_v Dmaj asm_v max_w Damaj asm_w True]
    show ?thesis .
  next
    case False
    from valueChosen_equal_case[OF max_w Damaj asm_w max_v Dmaj asm_v] False
    show ?thesis
      by auto
  qed
qed

lemma HEndPhase2_Inv6_2:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv6 s"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  and inv3: "HInv3 s"
  and inv5: "HInv5_inner s p"
  and asm: "outpt s' r \<noteq> NotAnInput"
  shows "outpt s' r = chosen s'"
proof(cases "chosen s=NotAnInput")
  case True
  with inv2c
  have "\<forall>q. outpt s q = NotAnInput"
    by(auto simp add: Inv2c_def Inv2c_inner_def)
  with True act asm
  show ?thesis
    by(auto simp add: EndPhase2_def HNextPart_def 
               split: if_split_asm)
next
  case False
  with inv
  have p31: "valueChosen s (chosen s)"
    by(auto simp add: HInv6_def)
  with False act
  have "chosen s'\<noteq> NotAnInput"
    by(auto simp add: HNextPart_def)
  from HEndPhase2_Inv6_1[OF act inv inv2b inv2c inv3 inv5 this]
  have p32: "valueChosen s'(chosen s')" .
  from False InputsOrNi
  have "chosen s \<in> Inputs" by auto
  from valueChosen_equal[OF HEndPhase2_valueChosen[OF act p31 this] p32]
  have p33: "chosen s = chosen s'" .
  from act
  have maj: "IsMajority {d .    d \<in> disksWritten s p
                             \<and> (\<forall>q \<in> UNIV - {p}. hasRead s p d q)}" (is "IsMajority ?D")
    and phase: "phase s p = 2"
    by(auto simp add: EndPhase2_def)  
  show ?thesis
  proof(cases "outpt s r = NotAnInput")
    case True
    with asm act
    have p41: "r=p"
      by(auto simp add: EndPhase2_def split: if_split_asm)
    from maj 
    have p42: "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. \<forall>q\<in>UNIV-{p}. hasRead s p d q"
      by(auto simp add: MajoritySet_def)
    have p43: "\<not>(\<exists>D\<in>MajoritySet. \<exists>q. (\<forall>d\<in>D.    bal(dblock s p) < mbal(disk s d q)
                                             \<and> \<not>hasRead s p d q))"     
    proof auto
      fix D q
      assume Dmaj: "D \<in> MajoritySet"
      show "\<exists>d\<in>D. bal (dblock s p) < mbal (disk s d q) \<longrightarrow> hasRead s p d q"
      proof(cases "p=q")
        assume pq: "p=q"
        thus ?thesis
        proof auto
          from maj majorities_intersect Dmaj
          have "?D\<inter>D\<noteq>{}"
            by(auto simp add: MajoritySet_def)
          hence "\<exists>d\<in>?D\<inter>D. d\<in> disksWritten s p" by auto
          then obtain d where d: "d\<in> disksWritten s p" and "d\<in>?D\<inter>D"
            by auto
          hence dD: "d\<in>D" by auto
          from d inv2b
          have "disk s d p = dblock s p"
            by(auto simp add: Inv2b_def Inv2b_inner_def)
          with inv2c phase
          have "bal(dblock s p) = mbal(disk s d p) "
            by(auto simp add: Inv2c_def Inv2c_inner_def)
          with dD pq
          show  "\<exists>d\<in>D. bal (dblock s q) < mbal (disk s d q) \<longrightarrow> hasRead s q d q"
            by auto
        qed
      next
        case False
        with p42
        have "\<exists>D\<in>MajoritySet. \<forall>d\<in>D. hasRead s p d q"
          by auto
        with majorities_intersect Dmaj
        show ?thesis
          by(auto simp add: MajoritySet_def, blast)
      qed
    qed
    with inv5 act
    have p44: "maxBalInp s (bal(dblock s p)) (inp(dblock s p))"
      by(auto simp add: EndPhase2_def HInv5_inner_def 
                        HInv5_inner_R_def)
    have "\<exists>bk\<in>allBlocks s. \<exists>b\<in>(UN p. Ballot p). (maxBalInp s b (chosen s)) \<and> b\<le> bal bk"
    proof -
      have disk_allblks: "\<forall>d p. disk s d p \<in> allBlocks s"
        by(auto simp add: allBlocks_def blocksOf_def)
      from p31
      have "\<exists>b\<in> (UN p. Ballot p). maxBalInp s b (chosen s) \<and> 
      (\<exists>p. \<exists>D\<in>MajoritySet.(\<forall>d\<in>D.  b \<le> bal(disk s d p)))"
        by(auto simp add: valueChosen_def, force)
      with majority_nonempty obtain b p D d
        where "IsMajority D \<and> b\<in> (UN p. Ballot p) \<and>  
               maxBalInp s b (chosen s) \<and> d\<in>D \<and> b \<le> bal(disk s d p)"
        by(auto simp add: MajoritySet_def, blast)
      with disk_allblks
      show ?thesis
        by(auto)
    qed
    then obtain bk b
      where p45_bk: "bk\<in>allBlocks s \<and> b\<le> bal bk" 
        and p45_b: "b\<in>(UN p. Ballot p) \<and> (maxBalInp s b (chosen s))"
      by auto
    have p46: "inp(dblock s p) = chosen s"
    proof(cases "b \<le> bal(dblock s p)")
      case True
      have "dblock s p \<in> allBlocks s"
        by(auto simp add: allBlocks_def blocksOf_def)
      with p45_b True
      show ?thesis
        by(auto simp add: maxBalInp_def)
    next
      case False
      from p44 p45_bk False
      have "inp bk = inp(dblock s p)"
        by(auto simp add: maxBalInp_def)
      with p45_b p45_bk
      show ?thesis
        by(auto simp add: maxBalInp_def)
    qed
    with p41 p33 act
    show ?thesis
      by(auto simp add: EndPhase2_def)
  next
    case False
    from inv2c
    have "Inv2c_inner s r"
      by(auto simp add: Inv2c_def)
    with False asm inv2c act
    have "outpt s' r = outpt s r"
      by(auto simp add: Inv2c_inner_def EndPhase2_def 
                 split: if_split_asm)
    with inv p33 False
    show ?thesis
      by(auto simp add: HInv6_def)
  qed
qed

theorem HEndPhase2_Inv6:
  assumes act: "HEndPhase2 s s' p"
  and inv: "HInv6 s"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  and inv3: "HInv3 s"
  and inv5: "HInv5_inner s p"
  shows "HInv6 s'"
proof(auto simp add: HInv6_def)
  assume "chosen s' \<noteq> NotAnInput"
  from HEndPhase2_Inv6_1[OF act inv inv2b inv2c inv3 inv5 this]
  show "valueChosen s' (chosen s')" .
next
  fix p
  assume "outpt s' p\<noteq> NotAnInput"
  from HEndPhase2_Inv6_2[OF act inv inv2b inv2c inv3 inv5 this] 
  show "outpt s' p = chosen s'" .
qed

lemma outpt_chosen:
  assumes outpt: "outpt s = outpt s'"
  and inv2c: "Inv2c s"
  and nextp: "HNextPart s s'"
  shows "chosen s' = chosen s"
proof -
  from inv2c
  have "chosen s = NotAnInput \<longrightarrow> (\<forall>p. outpt s p = NotAnInput)"
    by(auto simp add: Inv2c_inner_def Inv2c_def)
  with outpt nextp
  show ?thesis
    by(auto simp add: HNextPart_def)
qed

lemma outpt_Inv6: 
  "\<lbrakk> outpt s = outpt s'; \<forall>p. outpt s p \<in> {chosen s, NotAnInput};
     Inv2c s; HNextPart s s' \<rbrakk> \<Longrightarrow> \<forall>p. outpt s' p \<in> {chosen s', NotAnInput}"
  using outpt_chosen
  by auto

theorem HStartBallot_Inv6:
  assumes act: "HStartBallot s s' p"
  and inv: "HInv6 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: StartBallot_def HInv6_def)
  from HStartBallot_valueChosen[OF act] this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: StartBallot_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

theorem HPhase1or2Write_Inv6:
  assumes act: "HPhase1or2Write s s' p d"
  and inv: "HInv6 s"
  and inv4: "HInv4a s p"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: Phase1or2Write_def HInv6_def)
  from HPhase1or2Write_valueChosen[OF act] inv4 this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: Phase1or2Write_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

theorem HPhase1or2ReadThen_Inv6:
  assumes act: "HPhase1or2ReadThen s s' p d q"
  and inv: "HInv6 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: Phase1or2ReadThen_def HInv6_def)
  from HPhase1or2ReadThen_valueChosen[OF act] this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: Phase1or2ReadThen_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

theorem HPhase1or2ReadElse_Inv6:
  assumes act: "HPhase1or2ReadElse s s' p d q"
  and inv: "HInv6 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
  using assms and HStartBallot_Inv6
  by(auto simp add: Phase1or2ReadElse_def)

theorem HEndPhase1_Inv6:
  assumes act: "HEndPhase1 s s' p"
  and inv: "HInv6 s"
  and inv1: "Inv1 s"
  and inv2a: "Inv2a s"
  and inv2b: "Inv2b s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: EndPhase1_def HInv6_def)
  from HEndPhase1_valueChosen[OF act] inv1 inv2a inv2b this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: EndPhase1_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

lemma outpt_chosen_2:
  assumes outpt: "outpt s' = (outpt s) (p:= NotAnInput)"
  and inv2c: "Inv2c s"
  and nextp: "HNextPart s s'"
  shows "chosen s = chosen s'"
proof -
  from inv2c
  have "chosen s = NotAnInput \<longrightarrow> (\<forall>p. outpt s p = NotAnInput)"
    by(auto simp add: Inv2c_inner_def Inv2c_def)
  with outpt nextp
  show ?thesis
    by(auto simp add: HNextPart_def)
qed

lemma outpt_HInv6_2:
  assumes outpt: "outpt s' = (outpt s) (p:= NotAnInput)"
  and inv: "\<forall>p. outpt s p \<in> {chosen s, NotAnInput}"
  and inv2c: "Inv2c s"
  and nextp: "HNextPart s s'"
  shows "\<forall>p. outpt s' p \<in> {chosen s', NotAnInput}"
proof -
  from outpt_chosen_2[OF outpt inv2c nextp]
  have "chosen s = chosen s'" .
  with inv outpt
  show ?thesis
    by auto
qed

theorem HFail_Inv6:
  assumes act: "HFail s s' p"
  and inv: "HInv6 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen_2 act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: Fail_def HInv6_def)
  from HFail_valueChosen[OF act] this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s' = (outpt s) (p:=NotAnInput) "
    by(auto simp add: Fail_def)
  from outpt_HInv6_2[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

theorem HPhase0Read_Inv6:
  assumes act: "HPhase0Read s s' p d"
  and inv: "HInv6 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: Phase0Read_def HInv6_def)
  from HPhase0Read_valueChosen[OF act] this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: Phase0Read_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

theorem HEndPhase0_Inv6:
  assumes act: "HEndPhase0 s s' p"
  and inv: "HInv6 s"
  and inv1: "Inv1 s"
  and inv2c: "Inv2c s"
  shows "HInv6 s'"
proof -
  from outpt_chosen act inv2c inv
  have "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s (chosen s')"
    by(auto simp add: EndPhase0_def HInv6_def)
  from HEndPhase0_valueChosen[OF act] inv1 this InputsOrNi
  have t1: "chosen s' \<noteq> NotAnInput \<longrightarrow> valueChosen s' (chosen s')"
    by auto
  from act
  have outpt: "outpt s = outpt s'"
    by(auto simp add: EndPhase0_def)
  from outpt_Inv6[OF outpt] act inv2c inv
  have "\<forall>p. outpt s' p = chosen s' \<or> outpt s' p = NotAnInput"
    by(auto simp add: HInv6_def)
  with t1
  show ?thesis
    by(simp add: HInv6_def)
qed

text\<open>
  $HInv1 \wedge HInv2 \wedge HInv2' \wedge HInv3 \wedge HInv4 \wedge HInv5 \wedge HInv6$ 
  is an invariant of $HNext$.
\<close>

lemma I2f:
  assumes nxt: "HNext s s'"
  and inv: "HInv1 s \<and> HInv2 s \<and> HInv2 s' \<and> HInv3 s \<and> HInv4 s \<and> HInv5 s \<and> HInv6 s"
  shows "HInv6 s'" using assms
  by(auto simp add: HNext_def Next_def,
     auto simp add: HInv2_def intro: HStartBallot_Inv6,
     auto intro: HPhase0Read_Inv6,
     auto simp add: HInv4_def intro: HPhase1or2Write_Inv6,
     auto simp add: Phase1or2Read_def
          intro: HPhase1or2ReadThen_Inv6
                 HPhase1or2ReadElse_Inv6,
     auto simp add: EndPhase1or2_def HInv1_def HInv5_def
          intro: HEndPhase1_Inv6
                 HEndPhase2_Inv6,
     auto intro: HFail_Inv6,
     auto intro: HEndPhase0_Inv6)

end

