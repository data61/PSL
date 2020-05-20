(*  Title:       Proving the Correctness of Disk Paxos

    Author:      Mauro J. Jaskelioff, Stephan Merz, 2005
    Maintainer:  Mauro J. Jaskelioff <mauro at fceia.unr.edu.ar>
*)

theory DiskPaxos imports DiskPaxos_Invariant begin

subsection \<open>Inner Module\<close>

record
Istate =
  iinput :: "Proc \<Rightarrow> InputsOrNi"
  ioutput :: "Proc \<Rightarrow> InputsOrNi"
  ichosen :: InputsOrNi
  iallInput :: "InputsOrNi set"

definition IInit :: "Istate \<Rightarrow> bool"
where
  "IInit s =  (range (iinput s) \<subseteq> Inputs
             \<and> ioutput s = (\<lambda>p. NotAnInput)
             \<and> ichosen s = NotAnInput
             \<and> iallInput s = range (iinput s))"

definition IChoose :: "Istate \<Rightarrow> Istate \<Rightarrow> Proc \<Rightarrow> bool"
where
  "IChoose s s' p = (ioutput s p = NotAnInput
                   \<and> (if (ichosen s = NotAnInput)
                        then (\<exists>ip \<in> iallInput s.  ichosen s' = ip
                                            \<and> ioutput s' = (ioutput s) (p := ip))
                        else (  ioutput s' = (ioutput s) (p:= ichosen s)
                               \<and> ichosen s' = ichosen s))
                    \<and> iinput s' = iinput s \<and> iallInput s'= iallInput s)"

definition IFail :: "Istate \<Rightarrow> Istate \<Rightarrow> Proc \<Rightarrow> bool"
where
  "IFail s s' p =   (ioutput s' = (ioutput s) (p:= NotAnInput)
                  \<and> (\<exists>ip \<in> Inputs.  iinput s' = (iinput s)(p:= ip)
                                   \<and> iallInput s' = iallInput s \<union> {ip})
                  \<and> ichosen s' = ichosen s)"

definition INext :: "Istate \<Rightarrow> Istate \<Rightarrow> bool"
  where "INext s s' = (\<exists>p. IChoose s s' p \<or> IFail s s' p)"

definition s2is :: "state \<Rightarrow> Istate"
where
  "s2is s = \<lparr>iinput = inpt s, 
             ioutput = outpt s, 
             ichosen=chosen s,
             iallInput = allInput s\<rparr>"

theorem R1:
  "\<lbrakk> HInit s; is = s2is s\<rbrakk> \<Longrightarrow> IInit is"
  by(auto simp add: HInit_def IInit_def s2is_def Init_def)

theorem R2b:
  assumes inv: "HInv s"
  and inv': "HInv s'"
  and nxt: "HNext s s'"
  and srel: "is=s2is s \<and> is'=s2is s'"
  shows "(\<exists>p. IFail is is' p \<or> IChoose is is' p) \<or> is = is'"
proof(auto)
  assume chg_vars: "is\<noteq>is'"
  with srel
  have s_change: "   inpt s \<noteq> inpt s' \<or> outpt s \<noteq> outpt s' 
                  \<or> chosen s \<noteq> chosen s' \<or> allInput s \<noteq> allInput s'"
    by(auto simp add: s2is_def)
  from inv
  have inv2c5: "\<forall>p.   inpt s p \<in> allInput s 
                    \<and> (chosen s = NotAnInput \<longrightarrow> outpt s p = NotAnInput)"
    by(auto simp add: HInv_def HInv2_def Inv2c_def Inv2c_inner_def) 
  from nxt s_change inv2c5
  have "inpt s' \<noteq> inpt s \<or> outpt s' \<noteq> outpt s"
    by(auto simp add: HNext_def Next_def HNextPart_def)
  with nxt
  have "\<exists>p. Fail s s' p \<or> EndPhase2 s s' p"
    by(auto simp add: HNext_def Next_def 
      StartBallot_def Phase0Read_def Phase1or2Write_def 
      Phase1or2Read_def Phase1or2ReadThen_def Phase1or2ReadElse_def 
      EndPhase1or2_def EndPhase1_def EndPhase0_def)
  then obtain p where fail_or_endphase2: "Fail s s' p \<or> EndPhase2 s s' p"
    by auto
  from inv
  have inv2c: "Inv2c_inner s p"
    by(auto simp add: HInv_def HInv2_def Inv2c_def)
  from fail_or_endphase2 have "IFail is is' p \<or> IChoose is is' p"
  proof
    assume fail: "Fail s s' p "
    hence phase': "phase s' p = 0"
      and  outpt: "outpt s' = (outpt s) (p:= NotAnInput)"
      by(auto simp add: Fail_def)
    have "IFail is is' p"
    proof -
      from fail srel
      have "ioutput is' = (ioutput is) (p:= NotAnInput)"
        by(auto simp add: Fail_def s2is_def)
      moreover
      from nxt 
      have all_nxt: "allInput s'= allInput s \<union> (range (inpt s'))"
        by(auto simp add: HNext_def HNextPart_def)
      from fail srel
      have "\<exists>ip \<in> Inputs.  iinput is' = (iinput is)(p:= ip)"
        by(auto simp add: Fail_def s2is_def)
      then obtain ip where ip_Input: "ip\<in>Inputs" and "iinput is' = (iinput is)(p:= ip)"
        by auto
      with inv2c5 srel all_nxt
      have "  iinput is' = (iinput is)(p:= ip)
        \<and> iallInput is' = iallInput is \<union> {ip}"
        by(auto simp add: s2is_def)
      moreover
      from outpt srel nxt inv2c
      have "ichosen is' = ichosen is"
        by(auto simp add: HNext_def HNextPart_def s2is_def Inv2c_inner_def)
      ultimately
      show ?thesis
        using ip_Input
        by(auto simp add: IFail_def)
    qed
    thus ?thesis
      by auto
  next
    assume endphase2: "EndPhase2 s s' p"
    from endphase2
    have "phase s p =2"
      by(auto simp add: EndPhase2_def)
    with inv2c Ballot_nzero
    have bal_dblk_nzero: "bal(dblock s p)\<noteq> 0"
      by(auto simp add: Inv2c_inner_def)
    moreover
    from inv
    have inv2a_dblock: "Inv2a_innermost s p (dblock s p)"
      by(auto simp add: HInv_def HInv2_def Inv2a_def Inv2a_inner_def blocksOf_def)
    ultimately
    have p22: "inp (dblock s p) \<in> allInput s"
      by(auto simp add: Inv2a_innermost_def)
    from inv
    have "allInput s \<subseteq> Inputs"
      by(auto simp add: HInv_def HInv1_def)
    with p22 NotAnInput endphase2
    have outpt_nni: "outpt s' p \<noteq> NotAnInput"
      by(auto simp add: EndPhase2_def)
    show ?thesis
    proof(cases "chosen s = NotAnInput")
      case True
      with inv2c5
      have p31: "\<forall>q. outpt s q = NotAnInput"
        by auto
      with endphase2
      have p32: "\<forall>q \<in> UNIV -{p}. outpt s' q = NotAnInput"
        by(auto simp add: EndPhase2_def)
      hence some_eq: "(\<And>x. outpt s' x \<noteq> NotAnInput \<Longrightarrow> x = p)"
        by auto
      from p32 True nxt some_equality[of "\<lambda>p. outpt s' p \<noteq> NotAnInput", OF outpt_nni some_eq]
      have p33: "chosen s' = outpt s' p"
        by(auto simp add: HNext_def HNextPart_def)
      with endphase2
      have "chosen s' = inp(dblock s p) \<and> outpt s' = (outpt s)(p:=inp(dblock s p))"
        by(auto simp add: EndPhase2_def)
      with True p22 
      have "if (chosen s = NotAnInput)
                        then (\<exists>ip \<in> allInput s.  chosen s' = ip
                                            \<and> outpt s' = (outpt s) (p := ip))
                        else (  outpt s' = (outpt s) (p:= chosen s)
                               \<and> chosen s' = chosen s)"
        by auto
      moreover
      from endphase2 inv2c5 nxt
      have "inpt s' = inpt s \<and> allInput s'= allInput s"
        by(auto simp add: EndPhase2_def HNext_def HNextPart_def)
      ultimately
      show ?thesis
        using srel p31
        by(auto simp add: IChoose_def s2is_def)
    next
      case False
      with nxt
      have p31: "chosen s' = chosen s"
        by(auto simp add: HNext_def HNextPart_def)
      from inv'
      have inv6: "HInv6 s'"
        by(auto simp add: HInv_def)
      have p32: "outpt s' p = chosen s"
      proof-
        from endphase2
        have "outpt s' p  = inp(dblock s p)"
          by(auto simp add: EndPhase2_def)
        moreover
        from inv6 p31
        have "outpt s' p \<in> {chosen s, NotAnInput}"
          by(auto simp add: HInv6_def)
        ultimately
        show ?thesis
          using outpt_nni
          by auto
      qed
      from srel False
      have "IChoose is is' p"
      proof(clarsimp simp add: IChoose_def s2is_def)
        from endphase2 inv2c
        have "outpt s p = NotAnInput"
          by(auto simp add: EndPhase2_def Inv2c_inner_def)
        moreover
        from endphase2 p31 p32 False
        have "outpt s' = (outpt s) (p:= chosen s) \<and> chosen s' = chosen s"
          by(auto simp add: EndPhase2_def)
        moreover
        from endphase2 nxt inv2c5
        have "inpt s' = inpt s \<and> allInput s'= allInput s"
          by(auto simp add: EndPhase2_def HNext_def HNextPart_def)
        ultimately
        show "  outpt s p = NotAnInput 
              \<and> outpt s' = (outpt s)(p := chosen s) \<and> chosen s' = chosen s 
              \<and> inpt s' = inpt s \<and> allInput s' = allInput s"
          by auto
      qed
      thus ?thesis
        by auto
    qed
  qed
  thus "\<exists>p. IFail is is' p \<or> IChoose is is' p"
    by auto
qed

end

