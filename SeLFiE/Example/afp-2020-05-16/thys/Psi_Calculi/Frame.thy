(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Frame
  imports Agent
begin

lemma permLength[simp]:
  fixes p    :: "name prm"
  and   xvec :: "'a::pt_name list"

  shows "length(p \<bullet> xvec) = length xvec"
by(induct xvec) auto

nominal_datatype 'assertion frame =
    FAssert "'assertion::fs_name"
  | FRes "\<guillemotleft>name\<guillemotright> ('assertion frame)" ("\<lparr>\<nu>_\<rparr>_" [80, 80] 80)

primrec frameResChain :: "name list \<Rightarrow> ('a::fs_name) frame \<Rightarrow> 'a frame" where
  base: "frameResChain [] F = F"
| step: "frameResChain (x#xs) F = \<lparr>\<nu>x\<rparr>(frameResChain xs F)"

notation frameResChain ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80)
notation FAssert  ("\<langle>\<epsilon>, _\<rangle>" [80] 80)
abbreviation FAssertJudge ("\<langle>_, _\<rangle>" [80, 80] 80) where "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<equiv> frameResChain A\<^sub>F (FAssert \<Psi>\<^sub>F)"

lemma frameResChainEqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>F) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> F)"
by(induct_tac xvec, auto)

lemma frameResChainFresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "x \<sharp> \<lparr>\<nu>*xvec\<rparr>F = (x \<in> set xvec \<or> x \<sharp> F)"
by (induct xvec) (simp_all add: abs_fresh)

lemma frameResChainFreshSet: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> F)"
by (simp add: fresh_star_def frameResChainFresh)

lemma frameChainAlpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   F    :: "'a::fs_name frame"

  assumes xvecFreshF: "(p \<bullet> xvec) \<sharp>* F"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>F = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> F)"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frameResChainFreshSet)
  moreover from xvecFreshF have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*xvec\<rparr>F)"
    by (simp add: frameResChainFreshSet) (simp add: fresh_star_def)
  ultimately have "\<lparr>\<nu>*xvec\<rparr>F = p \<bullet> (\<lparr>\<nu>*xvec\<rparr>F)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma frameChainAlpha':
  fixes p    :: "name prm"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: "'a::fs_name"

  assumes "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P"
  and     S: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)"

  shows "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
using assms
by(subst frameChainAlpha) (auto simp add: fresh_star_def)

lemma alphaFrameRes:
  fixes x :: name
  and   F :: "'a::fs_name frame"
  and   y :: name

  assumes "y \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F)"
proof(cases "x = y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with \<open>y \<sharp> F\<close> show ?thesis
    by(perm_simp add: frame.inject alpha calc_atm fresh_left)
qed

lemma frameChainAppend:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'a::fs_name frame"
  
  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>F = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F)"
by(induct xvec) auto

lemma frameChainEqLength:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      with IH \<open>length xvec' = n\<close> have "length xvec' = length yvec'"
        by blast
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with IH \<open>length xvec' = n\<close> have "length xvec' = length ([(x, y)] \<bullet> yvec')"
        by blast
      hence "length xvec' = length yvec'"
        by simp
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      show ?case by simp
    qed
  qed
qed

lemma frameEqFresh:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<sharp> F"
  
  shows "y \<sharp> G"
using assms
by(auto simp add: frame.inject alpha fresh_left calc_atm)  

lemma frameEqSupp:
  fixes F :: "('a::fs_name) frame"
  and   G :: "'a frame"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>F = \<lparr>\<nu>y\<rparr>G"
  and     "x \<in> supp F"
  
  shows "y \<in> supp G"
using assms
apply(auto simp add: frame.inject alpha fresh_left calc_atm)
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts calc_atm)

lemma frameChainEqSuppEmpty[dest]:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "supp \<Psi> = ({}::name set)"

  shows "\<Psi> = \<Psi>'"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case  using \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close>
      by(simp add: frame.inject) 
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; supp \<Psi> = ({}::name set); n = length xvec\<rbrakk> \<Longrightarrow> \<Psi> = \<Psi>'"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      with IH \<open>length xvec' = n\<close> \<open>supp \<Psi> = {}\<close> show ?case
        by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xvec', \<Psi>\<rangle> = [(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>"
        by(simp add: alpha frame.inject)
      hence "\<langle>xvec', \<Psi>\<rangle> = \<langle>([(x, y)] \<bullet> yvec'), ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with IH \<open>length xvec' = n\<close> \<open>supp \<Psi> = {}\<close> have "\<Psi> = [(x, y)] \<bullet> \<Psi>'"
        by(simp add: eqvts)
      moreover with \<open>supp \<Psi> = {}\<close> have "supp([(x, y)] \<bullet> \<Psi>') = ({}::name set)"
        by simp
      hence "x \<sharp> ([(x, y)] \<bullet> \<Psi>')" and "y \<sharp> ([(x, y)] \<bullet> \<Psi>')"
        by(simp add: fresh_def)+
      with \<open>x \<noteq> y\<close> have "x \<sharp> \<Psi>'" and "y \<sharp> \<Psi>'"
        by(simp add: fresh_left calc_atm)+
      ultimately show ?case by simp
    qed
  qed
qed

lemma frameChainEq:
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "distinctPerm p" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; distinctPerm p; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  \<Psi>' = p \<bullet> \<Psi>"
      by fact

    from EQ \<open>x \<noteq> y\<close> have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                     and xFresh\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by(simp add: frame.inject alpha)+

    show ?case
    proof(case_tac "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
      assume "x \<sharp> \<langle>xvec', \<Psi>\<rangle>"
      with EQ have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
        by(rule frameEqFresh)
      with xFresh\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
        by(simp)
      with \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close> IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p"  and "\<Psi>' = p \<bullet> \<Psi>"
        by blast
      from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>distinctPerm p\<close> \<open>\<Psi>' = p \<bullet> \<Psi>\<close>
      show ?case by blast
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>))"
      hence xSupp\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
        by(simp add: fresh_def)
      with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
        by(rule frameEqSupp)
      hence "y \<sharp> yvec'"
        by(induct yvec') (auto simp add: frame.supp abs_supp)      
      with \<open>x \<sharp> yvec'\<close> EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
        by(simp add: eqvts)
      with  \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close> IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
        by blast

      from xSupp\<Psi> have "x \<sharp> xvec'"
        by(induct xvec') (auto simp add: frame.supp abs_supp)      
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
        apply(induct p)
        by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
      from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
        by force
      moreover from \<open>x \<noteq> y\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> S \<open>distinctPerm p\<close>
      have "distinctPerm((x,y)#p)" by simp
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
        by(simp add: eqvts calc_atm freshChainSimps)
      moreover from \<open>([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>\<close>
      have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
        by(simp add: pt_bij)
      hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
      ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
        by blast
    qed
  qed
  ultimately show ?thesis by blast
qed
(*
lemma frameChainEq'':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (yvec)" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from `0 = length xvec` have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from `Suc n = length xvec`
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from `\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>` `xvec = x # xvec'`
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; n = length xvec\<rbrakk> \<Longrightarrow>
                                 \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    show ?case
    proof(cases "x=y")
      case True
      from EQ `x = y` have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" by(simp add: alpha frame.inject)
      then obtain p where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "\<Psi>' = p \<bullet> \<Psi>" using `length xvec' = n` IH
        by blast
      from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set (y#yvec')" by auto
      moreover from `x = y` `\<Psi>' = p \<bullet> \<Psi>` have "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by auto
      ultimately show ?thesis using `xvec = x#xvec'` `yvec = y#yvec'` by blast
    next
      case False
      from EQ `x \<noteq> y` have EQ': "\<langle>xvec', \<Psi>\<rangle> = ([(x, y)] \<bullet> \<langle>yvec', \<Psi>'\<rangle>)" 
                       and xFresh\<Psi>': "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
        by(simp add: frame.inject alpha)+
    
      show ?thesis
      proof(cases "x \<sharp> \<langle>xvec', \<Psi>\<rangle>")
        case True
        from EQ `x \<sharp> \<langle>xvec', \<Psi>\<rangle>` have "y \<sharp> \<langle>yvec', \<Psi>'\<rangle>"
          by(rule frameEqFresh)
        with xFresh\<Psi>' EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', \<Psi>'\<rangle>" 
          by(simp)
        with `length xvec' = n` IH
        obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "\<Psi>' = p \<bullet> \<Psi>"
          by blast
        from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
        with `xvec = x#xvec'` `yvec=y#yvec'` `\<Psi>' = p \<bullet> \<Psi>`
        show ?thesis by blast
      next
        case False
        from `\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>))` have xSupp\<Psi>: "x \<in> supp(\<langle>xvec', \<Psi>\<rangle>)"
          by(simp add: fresh_def)
        with EQ have "y \<in> supp (\<langle>yvec', \<Psi>'\<rangle>)"
          by(rule frameEqSupp)
        hence "y \<sharp> yvec'"
          by(induct yvec') (auto simp add: frame.supp abs_supp)

        with `x \<sharp> yvec'` EQ' have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
          by(simp add: eqvts)
        with  `xvec' \<sharp>* yvec'` `length xvec' = n` IH
        obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>"
          by blast
        
        from xSupp\<Psi> have "x \<sharp> xvec'"
          by(induct xvec') (auto simp add: frame.supp abs_supp)      
        with `x \<sharp> yvec'` `y \<sharp> xvec'` `y \<sharp> yvec'` S have "x \<sharp> p" and "y \<sharp> p"
          apply(induct p)
          by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
        from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
          by force
        moreover from `x \<noteq> y` `x \<sharp> p` `y \<sharp> p` S `distinctPerm p`
        have "distinctPerm((x,y)#p)" by simp
        moreover from `x \<sharp> p` `y \<sharp> p` `x \<sharp> xvec'` `y \<sharp> xvec'` have "y#(p \<bullet> xvec') = ((x, y)#p) \<bullet> (x#xvec')" 
          by(simp add: eqvts calc_atm freshChainSimps)
        moreover from `([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>`
        have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
          by(simp add: pt_bij)
        hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>" by simp
        ultimately show ?case using `xvec=x#xvec'` `yvec=y#yvec'`
          by blast
      qed
    qed
    ultimately show ?thesis by blast
qed
*)
lemma frameChainEq':
  fixes xvec :: "name list"
  and   \<Psi>    :: "'a::fs_name"
  and   yvec :: "name list"
  and   \<Psi>'   :: "'a::fs_name"

  assumes "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinctPerm p" and "yvec = p \<bullet> xvec" and "\<Psi>' = p \<bullet> \<Psi>"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinctPerm p; yvec = p \<bullet> xvec; \<Psi>' = p \<bullet> \<Psi>\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
  proof(induct n arbitrary: xvec yvec \<Psi> \<Psi>')
    case(0 xvec yvec \<Psi> \<Psi>')
    have Eq: "\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: frame.inject)
  next
    case(Suc n xvec yvec \<Psi> \<Psi>')
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<langle>xvec, \<Psi>\<rangle> = \<langle>yvec, \<Psi>'\<rangle>\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<langle>(x#xvec'), \<Psi>\<rangle> = \<langle>(y#yvec'), \<Psi>'\<rangle>"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xvec'\<rparr>(FAssert \<Psi>) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*yvec'\<rparr>(FAssert \<Psi>')"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec \<Psi> \<Psi>'. \<lbrakk>\<langle>xvec, (\<Psi>::'a)\<rangle> = \<langle>yvec, (\<Psi>'::'a)\<rangle>; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> \<Psi>' = p \<bullet> \<Psi>"
      by fact
    from EQ \<open>x \<noteq> y\<close>  \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> have "\<langle>xvec', \<Psi>\<rangle> = \<langle>yvec', ([(x, y)] \<bullet> \<Psi>')\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with \<open>xvec' \<sharp>* yvec'\<close> \<open>distinct xvec'\<close> \<open>distinct yvec'\<close> \<open>length xvec' = n\<close> IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "yvec' = p \<bullet> xvec'" and "[(x, y)] \<bullet> \<Psi>' = p \<bullet> \<Psi>"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from \<open>x \<sharp> xvec'\<close> \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: name_list_supp) (auto simp add: fresh_def) 

    with S \<open>distinctPerm p\<close> \<open>x \<noteq> y\<close> have "distinctPerm((x, y)#p)" by auto
    moreover from \<open>yvec' = p \<bullet> xvec'\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: freshChainSimps calc_atm)
    moreover from \<open>([(x, y)] \<bullet> \<Psi>') = p \<bullet> \<Psi>\<close>
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> p \<bullet> \<Psi>"
      by(simp add: pt_bij)
    hence "\<Psi>' = ((x, y)#p) \<bullet> \<Psi>"
      by simp
    ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma frameEq[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>  :: "'a::fs_name"
  and   \<Psi>'  :: 'a

  shows "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
  and   "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^sub>F, \<Psi>\<rangle>  = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
proof -
  {
    assume "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle>"
    hence A: "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>[], \<Psi>'\<rangle>" by simp
    hence "length A\<^sub>F = length ([]::name list)"
      by(rule frameChainEqLength)
    with A have "A\<^sub>F = []" and "\<Psi> = \<Psi>'" by(auto simp add: frame.inject)
  }
  thus "\<langle>A\<^sub>F, \<Psi>\<rangle> = \<langle>\<epsilon>, \<Psi>'\<rangle> = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
  and  "\<langle>\<epsilon>, \<Psi>'\<rangle> = \<langle>A\<^sub>F, \<Psi>\<rangle>  = (A\<^sub>F = [] \<and> \<Psi> = \<Psi>')"
    by auto
qed

lemma distinctFrame:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: "'a::fs_name"
  and   C  :: "'b::fs_name"
  
  assumes "A\<^sub>F \<sharp>* C"

  obtains A\<^sub>F' where  "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C"
proof -
  assume "\<And>A\<^sub>F'. \<lbrakk>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>; distinct A\<^sub>F'; A\<^sub>F' \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover from assms have "\<exists>A\<^sub>F'. \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle> \<and> distinct A\<^sub>F' \<and> A\<^sub>F' \<sharp>* C"
  proof(induct A\<^sub>F)
    case Nil
    thus ?case by simp
  next
    case(Cons a A\<^sub>F)
    then obtain A\<^sub>F' where Eq: "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F'" and "A\<^sub>F' \<sharp>* C" by force
    from \<open>(a#A\<^sub>F) \<sharp>* C\<close> have "a \<sharp> C" and "A\<^sub>F \<sharp>* C" by simp+
    show ?case
    proof(case_tac "a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>")
      assume "a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>"
      obtain b::name where "b \<sharp> A\<^sub>F'" and "b \<sharp> \<Psi>\<^sub>F" and "b \<sharp> C" by(generate_fresh "name", auto)
      have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(b#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>"
      proof -
        from Eq have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(a#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
        moreover from \<open>b \<sharp> \<Psi>\<^sub>F\<close> have "\<dots> = \<lparr>\<nu>b\<rparr>([(a, b)] \<bullet> \<lparr>\<nu>*A\<^sub>F'\<rparr>(FAssert \<Psi>\<^sub>F))"
          by(force intro: alphaFrameRes simp add: frameResChainFresh)
        ultimately show ?thesis using \<open>a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>\<close> \<open>b \<sharp> \<Psi>\<^sub>F\<close>
          by(simp add: frameResChainFresh)
      qed
      moreover from \<open>distinct A\<^sub>F'\<close> \<open>b \<sharp> A\<^sub>F'\<close> have "distinct(b#A\<^sub>F')" by simp
      moreover from \<open>A\<^sub>F' \<sharp>* C\<close> \<open>b \<sharp> C\<close> have "(b#A\<^sub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    next
      from Eq have "\<langle>(a#A\<^sub>F), \<Psi>\<^sub>F\<rangle> = \<langle>(a#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
      moreover assume "\<not>(a \<sharp> \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>)"
      hence "a \<sharp> A\<^sub>F'" apply(simp add: fresh_def)
        by(induct A\<^sub>F') (auto simp add: supp_list_nil supp_list_cons supp_atm frame.supp abs_supp)
      with \<open>distinct A\<^sub>F'\<close> have "distinct(a#A\<^sub>F')" by simp
      moreover from \<open>A\<^sub>F' \<sharp>* C\<close> \<open>a \<sharp> C\<close> have "(a#A\<^sub>F') \<sharp>* C" by simp+
      ultimately show ?case by blast
    qed
  qed
  ultimately show ?thesis using \<open>A\<^sub>F \<sharp>* C\<close>
    by blast
qed

lemma freshFrame:
  fixes F  :: "('a::fs_name) frame"
  and   C  :: "'b ::fs_name"

  obtains A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "distinct A\<^sub>F" and "A\<^sub>F \<sharp>* C"
proof -
  assume "\<And>A\<^sub>F \<Psi>\<^sub>F. \<lbrakk>F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; distinct A\<^sub>F; A\<^sub>F \<sharp>* C\<rbrakk> \<Longrightarrow> thesis"
  moreover have "\<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* C"
  proof(nominal_induct F avoiding: C rule: frame.strong_induct)
    case(FAssert \<Psi>\<^sub>F)
    have "FAssert \<Psi>\<^sub>F = \<langle>[], \<Psi>\<^sub>F\<rangle>" by simp
    moreover have "([]::name list) \<sharp>* C" by simp
    ultimately show ?case by force
  next
    case(FRes a F)
    from \<open>\<And>C. \<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* C\<close>
    obtain A\<^sub>F \<Psi>\<^sub>F  where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* C"
      by blast
    with \<open>a \<sharp> C\<close> have "\<lparr>\<nu>a\<rparr>F = \<lparr>\<nu>*(a#A\<^sub>F)\<rparr>(FAssert \<Psi>\<^sub>F)" and "(a#A\<^sub>F) \<sharp>* C"
      by simp+
    thus ?case by blast
  qed
  ultimately show ?thesis
    by(auto, rule_tac distinctFrame) auto
qed

locale assertionAux = 
  fixes SCompose :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"   (infixr "\<otimes>" 80)
  and   SImp     :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool" ("_ \<turnstile> _" [70, 70] 70)
  and   SBottom  :: 'b                         ("\<bottom>" 90) 
  and   SChanEq  :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c"   ("_ \<leftrightarrow> _" [80, 80] 80)

  assumes statEqvt[eqvt]:   "\<And>p::name prm. p \<bullet> (\<Psi> \<turnstile> \<Phi>) = (p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<Phi>)"
  and     statEqvt'[eqvt]:  "\<And>p::name prm. p \<bullet> (\<Psi> \<otimes> \<Psi>') = (p \<bullet> \<Psi>) \<otimes> (p \<bullet> \<Psi>')" 
  and     statEqvt''[eqvt]: "\<And>p::name prm. p \<bullet> (M \<leftrightarrow> N) = (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
  and     permBottom[eqvt]: "\<And>p::name prm. (p \<bullet> SBottom) = SBottom"

begin

lemma statClosed:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c
  and   p :: "name prm"
  
  assumes "\<Psi> \<turnstile> \<phi>"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> \<phi>)"
using assms statEqvt
by(simp add: perm_bool)

lemma compSupp:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(supp(\<Psi> \<otimes> \<Psi>')::name set) \<subseteq> ((supp \<Psi>) \<union> (supp \<Psi>'))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> \<Psi>) \<otimes> [(x, y)] \<bullet> \<Psi>' \<noteq> \<Psi> \<otimes> \<Psi>'"
  let ?Q = "\<lambda>y \<Psi>. ([(x, y)] \<bullet> \<Psi>) \<noteq> \<Psi>"
  assume "finite {y. ?Q y \<Psi>'}"
  moreover assume "finite {y. ?Q y \<Psi>}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y \<Psi>})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y \<Psi>}) - {y. ?Q y \<Psi>'})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y \<Psi>) \<and> \<not> (?Q y \<Psi>')} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma chanEqSupp:
  fixes M :: 'a
  and   N :: 'a

  shows "(supp(M \<leftrightarrow> N)::name set) \<subseteq> ((supp M) \<union> (supp N))"
proof(auto simp add: eqvts supp_def)
  fix x::name
  let ?P = "\<lambda>y. ([(x, y)] \<bullet> M) \<leftrightarrow> [(x, y)] \<bullet> N \<noteq> M \<leftrightarrow> N"
  let ?Q = "\<lambda>y M. ([(x, y)] \<bullet> M) \<noteq> M"
  assume "finite {y. ?Q y N}"
  moreover assume "finite {y. ?Q y M}" and "infinite {y. ?P(y)}"
  hence "infinite({y. ?P(y)} - {y. ?Q y M})" by(rule Diff_infinite_finite)
  ultimately have "infinite(({y. ?P(y)} - {y. ?Q y M}) - {y. ?Q y N})" by(rule Diff_infinite_finite)
  hence "infinite({y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)})" by(simp add: set_diff_eq)
  moreover have "{y. ?P(y) \<and> \<not>(?Q y M) \<and> \<not> (?Q y N)} = {}" by auto
  ultimately have "infinite {}" by(drule_tac Infinite_cong) auto
  thus False by simp
qed

lemma freshComp[intro]:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> \<Psi>'"

  shows "x \<sharp> \<Psi> \<otimes> \<Psi>'"
using assms compSupp
by(auto simp add: fresh_def)

lemma freshCompChain[intro]:
  fixes xvec  :: "name list"
  and   Xs    :: "name set"
  and   \<Psi>     :: 'b
  and   \<Psi>'    :: 'b

  shows "\<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> xvec \<sharp>* (\<Psi> \<otimes> \<Psi>')"
  and   "\<lbrakk>Xs \<sharp>* \<Psi>; Xs \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> Xs \<sharp>* (\<Psi> \<otimes> \<Psi>')"
by(auto simp add: fresh_star_def)

lemma freshChanEq[intro]:
  fixes x :: name
  and   M :: 'a
  and   N :: 'a

  assumes "x \<sharp> M"
  and     "x \<sharp> N"

  shows "x \<sharp> M \<leftrightarrow> N"
using assms chanEqSupp
by(auto simp add: fresh_def)

lemma freshChanEqChain[intro]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   M    :: 'a
  and   N    :: 'a

  shows "\<lbrakk>xvec \<sharp>* M; xvec \<sharp>* N\<rbrakk> \<Longrightarrow> xvec \<sharp>* (M \<leftrightarrow> N)"
  and   "\<lbrakk>Xs \<sharp>* M; Xs \<sharp>* N\<rbrakk> \<Longrightarrow> Xs \<sharp>* (M \<leftrightarrow> N)"
by(auto simp add: fresh_star_def)

lemma suppBottom[simp]:
  shows "((supp SBottom)::name set) = {}"
by(auto simp add: supp_def permBottom)

lemma freshBottom[simp]:
  fixes x :: name
  
  shows "x \<sharp> \<bottom>"
by(simp add: fresh_def)

lemma freshBottoChain[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>)"
  and   "Xs   \<sharp>* (\<bottom>)"
by(auto simp add: fresh_star_def)

lemma chanEqClosed:
  fixes \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   p :: "name prm"
 
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> N"

  shows "(p \<bullet> \<Psi>) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> N)"
proof -
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> N\<close> have "(p \<bullet> \<Psi>) \<turnstile> p \<bullet> (M \<leftrightarrow> N)"
    by(rule statClosed)
  thus ?thesis by(simp add: eqvts)
qed

definition
  AssertionStatImp :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<hookrightarrow>" 70)
  where "(\<Psi> \<hookrightarrow> \<Psi>') \<equiv> (\<forall>\<Phi>. \<Psi> \<turnstile> \<Phi> \<longrightarrow> \<Psi>' \<turnstile> \<Phi>)"

definition
  AssertionStatEq :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<simeq>" 70)
  where "(\<Psi> \<simeq> \<Psi>') \<equiv> \<Psi> \<hookrightarrow> \<Psi>' \<and> \<Psi>' \<hookrightarrow> \<Psi>"

lemma statImpEnt:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(simp add: AssertionStatImp_def)

lemma statEqEnt:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<Phi>  :: 'c

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi> \<turnstile> \<Phi>"

  shows "\<Psi>' \<turnstile> \<Phi>"
using assms
by(auto simp add: AssertionStatEq_def intro: statImpEnt)

lemma AssertionStatImpClosed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>')"
proof(auto simp add: AssertionStatImp_def)
  fix \<phi>
  assume "(p \<bullet> \<Psi>) \<turnstile> \<phi>"
  hence "\<Psi> \<turnstile> rev p \<bullet> \<phi>" by(drule_tac p="rev p" in statClosed) auto
  with \<open>\<Psi> \<hookrightarrow> \<Psi>'\<close> have "\<Psi>' \<turnstile> rev p \<bullet> \<phi>" by(simp add: AssertionStatImp_def)
  thus "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(drule_tac p=p in statClosed) auto
qed

lemma AssertionStatEqClosed:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')"
using assms
by(auto simp add: AssertionStatEq_def intro: AssertionStatImpClosed)

lemma AssertionStatImpEqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<hookrightarrow> \<Psi>')) = ((p \<bullet> \<Psi>) \<hookrightarrow> (p \<bullet> \<Psi>'))"
by(simp add: AssertionStatImp_def eqvts)

lemma AssertionStatEqEqvt[eqvt]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<simeq> \<Psi>')) = ((p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>'))"
by(simp add: AssertionStatEq_def eqvts)

lemma AssertionStatImpRefl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi>"
by(simp add: AssertionStatImp_def)

lemma AssertionStatEqRefl[simp]:
  fixes \<Psi> :: 'b

  shows "\<Psi> \<simeq> \<Psi>"
by(simp add: AssertionStatEq_def)

lemma AssertionStatEqSym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<simeq> \<Psi>"
using assms
by(auto simp add: AssertionStatEq_def)

lemma AssertionStatImpTrans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<hookrightarrow> \<Psi>'"
  and     "\<Psi>' \<hookrightarrow> \<Psi>''"

  shows "\<Psi> \<hookrightarrow> \<Psi>''"
using assms
by(simp add: AssertionStatImp_def)

lemma AssertionStatEqTrans:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>' \<simeq> \<Psi>''"

  shows "\<Psi> \<simeq> \<Psi>''"
using assms
by(auto simp add: AssertionStatEq_def intro: AssertionStatImpTrans)

definition 
  FrameImp :: "'b::fs_name frame \<Rightarrow> 'c \<Rightarrow> bool"   (infixl "\<turnstile>\<^sub>F" 70)
  where "(F \<turnstile>\<^sub>F \<Phi>) = (\<exists>A\<^sub>F \<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> A\<^sub>F \<sharp>* \<Phi> \<and> (\<Psi>\<^sub>F \<turnstile> \<Phi>))"

lemma frameImpI:
  fixes F  :: "'b frame"
  and   \<phi>  :: 'c
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
  and     "A\<^sub>F \<sharp>* \<phi>"
  and     "\<Psi>\<^sub>F \<turnstile> \<phi>"

  shows "F \<turnstile>\<^sub>F \<phi>"
using assms
by(force simp add: FrameImp_def)

lemma frameImpAlphaEnt:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>\<^sub>F  :: 'b
  and   A\<^sub>F' :: "name list"
  and   \<Psi>\<^sub>F' :: 'b
  and   \<phi>   :: 'c

  assumes "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>" 
  and     "A\<^sub>F \<sharp>* \<phi>"
  and     "A\<^sub>F' \<sharp>* \<phi>"
  and     "\<Psi>\<^sub>F' \<turnstile> \<phi>"

  shows "\<Psi>\<^sub>F \<turnstile> \<phi>"
proof -
  from \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>\<close>
  obtain n where "n = length A\<^sub>F" by blast
  moreover from \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>\<close>
  have "length A\<^sub>F = length A\<^sub>F'"
    by(rule frameChainEqLength)
  ultimately show ?thesis using assms
  proof(induct n arbitrary: A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F' rule: nat.induct)
    case(zero A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F')
    thus ?case by(auto simp add: frame.inject)
  next
    case(Suc n A\<^sub>F A\<^sub>F' \<Psi>\<^sub>F')
    from \<open>Suc n = length A\<^sub>F\<close>
    obtain x xs where "A\<^sub>F = x#xs" and "n = length xs"
      by(case_tac A\<^sub>F) auto
    from \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> = \<langle>A\<^sub>F', \<Psi>\<^sub>F'\<rangle>\<close> \<open>A\<^sub>F = x # xs\<close>
    obtain y ys where "\<langle>(x#xs), \<Psi>\<^sub>F\<rangle> = \<langle>(y#ys), \<Psi>\<^sub>F'\<rangle>" and "A\<^sub>F' = y#ys"
      by(case_tac A\<^sub>F') auto
    hence EQ: "\<lparr>\<nu>x\<rparr>\<lparr>\<nu>*xs\<rparr>(FAssert \<Psi>\<^sub>F) = \<lparr>\<nu>y\<rparr>\<lparr>\<nu>*ys\<rparr>(FAssert \<Psi>\<^sub>F')"
      by simp
    from \<open>A\<^sub>F = x # xs\<close> \<open>A\<^sub>F' = y # ys\<close> \<open>length A\<^sub>F = length A\<^sub>F'\<close> \<open>A\<^sub>F \<sharp>* \<phi>\<close> \<open>A\<^sub>F' \<sharp>* \<phi>\<close>
    have "length xs = length ys" and "xs \<sharp>* \<phi>" and "ys \<sharp>* \<phi>" and "x \<sharp> \<phi>" and "y \<sharp> \<phi>" 
      by auto
    
    have IH: "\<And>xs ys \<Psi>\<^sub>F'. \<lbrakk>n = length xs; length xs = length ys; \<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>ys, (\<Psi>\<^sub>F'::'b)\<rangle>; xs \<sharp>* \<phi>; ys \<sharp>* \<phi>; \<Psi>\<^sub>F' \<turnstile> \<phi>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>F \<turnstile> \<phi>"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>ys, \<Psi>\<^sub>F'\<rangle>" by(simp add: alpha frame.inject)
      with IH \<open>n = length xs\<close> \<open>length xs = length ys\<close> \<open>xs \<sharp>* \<phi>\<close>  \<open>ys \<sharp>* \<phi>\<close> \<open>\<Psi>\<^sub>F' \<turnstile> \<phi>\<close>
      show ?case by blast
    next
      assume "x \<noteq> y"
      with EQ have "\<langle>xs, \<Psi>\<^sub>F\<rangle> = [(x, y)] \<bullet> \<langle>ys, \<Psi>\<^sub>F'\<rangle>" by(simp add: alpha frame.inject)
      hence "\<langle>xs, \<Psi>\<^sub>F\<rangle> = \<langle>([(x, y)] \<bullet> ys), ([(x, y)] \<bullet> \<Psi>\<^sub>F')\<rangle>" by(simp add: eqvts)
      moreover from \<open>length xs = length ys\<close> have "length xs = length([(x, y)] \<bullet> ys)"
        by auto
      moreover from \<open>ys \<sharp>* \<phi>\<close> have "([(x, y)] \<bullet> ys) \<sharp>* ([(x, y)] \<bullet> \<phi>)"
        by(simp add: fresh_star_bij)
      with \<open>x \<sharp> \<phi>\<close> \<open>y \<sharp> \<phi>\<close> have "([(x, y)] \<bullet> ys) \<sharp>* \<phi>"
        by simp
      moreover with \<open>\<Psi>\<^sub>F' \<turnstile> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>\<^sub>F') \<turnstile> ([(x, y)] \<bullet> \<phi>)"
        by(simp add: statClosed)
      with \<open>x \<sharp> \<phi>\<close> \<open>y \<sharp> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>\<^sub>F') \<turnstile> \<phi>"
        by simp
      ultimately show ?case using IH \<open>n = length xs\<close> \<open>xs \<sharp>* \<phi>\<close>
        by blast
    qed
  qed
qed

lemma frameImpEAux:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "F \<turnstile>\<^sub>F \<Phi>"
  and      "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
  and      "A\<^sub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^sub>F \<turnstile> \<Phi>"
using assms
by(auto simp add: FrameImp_def dest: frameImpAlphaEnt)

lemma frameImpE:
  fixes F  :: "'b frame"
  and   \<Phi>  :: 'c

  assumes  "\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<Phi>"
  and      "A\<^sub>F \<sharp>* \<Phi>"
  
  shows "\<Psi>\<^sub>F \<turnstile> \<Phi>"
using assms
by(auto elim: frameImpEAux)

lemma frameImpClosed:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  assumes "F \<turnstile>\<^sub>F \<Phi>"

  shows "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
using assms
by(force simp add: FrameImp_def eqvts pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst]
         intro: statClosed)

lemma frameImpEqvt[eqvt]:
  fixes F :: "'b frame"
  and   \<Phi> :: 'c
  and   p :: "name prm"

  shows "(p \<bullet> (F \<turnstile>\<^sub>F \<Phi>)) = (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
proof -
  have "F \<turnstile>\<^sub>F \<Phi> \<Longrightarrow> (p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>)"
    by(rule frameImpClosed)
  moreover have "(p \<bullet> F) \<turnstile>\<^sub>F (p \<bullet> \<Phi>) \<Longrightarrow> F \<turnstile>\<^sub>F \<Phi>"
    by(drule_tac p = "rev p" in frameImpClosed) simp
  ultimately show ?thesis
    by(auto simp add: perm_bool)
qed

lemma frameImpEmpty[simp]:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<turnstile>\<^sub>F \<phi> = \<Psi> \<turnstile> \<phi>" 
by(auto simp add: FrameImp_def)

definition
  FrameStatImp :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<hookrightarrow>\<^sub>F" 70)
  where "(F \<hookrightarrow>\<^sub>F G) \<equiv> (\<forall>\<phi>. F \<turnstile>\<^sub>F \<phi> \<longrightarrow> G \<turnstile>\<^sub>F \<phi>)"

definition
  FrameStatEq :: "'b frame \<Rightarrow> 'b frame\<Rightarrow> bool" (infix "\<simeq>\<^sub>F" 70)
  where "(F \<simeq>\<^sub>F G) \<equiv> F \<hookrightarrow>\<^sub>F G \<and> G \<hookrightarrow>\<^sub>F F"

lemma FrameStatImpClosed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "(p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G)"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>
  assume "(p \<bullet> F) \<turnstile>\<^sub>F \<phi>"
  hence "F \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(drule_tac p="rev p" in frameImpClosed) auto
  with \<open>F \<hookrightarrow>\<^sub>F G\<close> have "G \<turnstile>\<^sub>F rev p \<bullet> \<phi>" by(simp add: FrameStatImp_def)
  thus "(p \<bullet> G) \<turnstile>\<^sub>F \<phi>" by(drule_tac p=p in frameImpClosed) auto
qed

lemma FrameStatEqClosed:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  assumes "F \<simeq>\<^sub>F G"

  shows "(p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G)"
using assms
by(auto simp add: FrameStatEq_def intro: FrameStatImpClosed)

lemma FrameStatImpEqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<hookrightarrow>\<^sub>F G)) = ((p \<bullet> F) \<hookrightarrow>\<^sub>F (p \<bullet> G))"
by(simp add: FrameStatImp_def eqvts)

lemma FrameStatEqEqvt[eqvt]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   p :: "name prm"

  shows "(p \<bullet> (F \<simeq>\<^sub>F G)) = ((p \<bullet> F) \<simeq>\<^sub>F (p \<bullet> G))"
by(simp add: FrameStatEq_def eqvts)

lemma FrameStatImpRefl[simp]:
  fixes F :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F"
by(simp add: FrameStatImp_def)

lemma FrameStatEqRefl[simp]:
  fixes F :: "'b frame"

  shows "F \<simeq>\<^sub>F F"
by(simp add: FrameStatEq_def)

lemma FrameStatEqSym:
  fixes F  :: "'b frame"
  and   G  :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"

  shows "G \<simeq>\<^sub>F F"
using assms
by(auto simp add: FrameStatEq_def)

lemma FrameStatImpTrans:
  fixes F :: "'b frame"
  and   G :: "'b frame" 
  and   H :: "'b frame"

  assumes "F \<hookrightarrow>\<^sub>F G"
  and     "G \<hookrightarrow>\<^sub>F H"

  shows "F \<hookrightarrow>\<^sub>F H"
using assms
by(simp add: FrameStatImp_def)

lemma FrameStatEqTrans:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   H :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"
  and     "G \<simeq>\<^sub>F H"

  shows "F \<simeq>\<^sub>F H"
using assms
by(auto simp add: FrameStatEq_def intro: FrameStatImpTrans)

lemma fsCompose[simp]: "finite((supp SCompose)::name set)"
by(simp add: supp_def perm_fun_def eqvts)

nominal_primrec 
   insertAssertion :: "'b frame \<Rightarrow> 'b \<Rightarrow> 'b frame"
where
  "insertAssertion (FAssert \<Psi>) \<Psi>' = FAssert (\<Psi>' \<otimes> \<Psi>)"
| "x \<sharp> \<Psi>' \<Longrightarrow> insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi>' = \<lparr>\<nu>x\<rparr>(insertAssertion F \<Psi>')"
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(rule supports_fresh[of "supp \<Psi>'"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

lemma insertAssertionEqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   \<Psi> :: 'b

  shows "p \<bullet> (insertAssertion F \<Psi>) = insertAssertion (p \<bullet> F) (p \<bullet> \<Psi>)"
by(nominal_induct F avoiding: p \<Psi> rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)


nominal_primrec 
   mergeFrame :: "'b frame \<Rightarrow> 'b frame \<Rightarrow> 'b frame"
where
  "mergeFrame (FAssert \<Psi>) G = insertAssertion G \<Psi>"
| "x \<sharp> G \<Longrightarrow> mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<lparr>\<nu>x\<rparr>(mergeFrame F G)"
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(simp add: fs_name1)
apply(rule supports_fresh[of "supp G"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
done

notation mergeFrame (infixr "\<otimes>\<^sub>F" 80)

abbreviation
  frameBottomJudge ("\<bottom>\<^sub>F") where "\<bottom>\<^sub>F \<equiv> (FAssert SBottom)"

lemma mergeFrameEqvt[eqvt]:
  fixes p :: "name prm"
  and   F :: "'b frame"
  and   G :: "'b frame"

  shows "p \<bullet> (mergeFrame F G) = mergeFrame (p \<bullet> F) (p \<bullet> G)"
by(nominal_induct F avoiding: p G rule: frame.strong_induct)
  (auto simp add: at_prm_fresh[OF at_name_inst] 
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst] eqvts)

nominal_primrec
    extractFrame   :: "('a, 'b, 'c) psi \<Rightarrow> 'b frame"
and extractFrame'  :: "('a, 'b, 'c) input \<Rightarrow> 'b frame"
and extractFrame'' :: "('a, 'b, 'c) psiCase \<Rightarrow> 'b frame"

where
  "extractFrame (\<zero>) =  \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (M\<lparr>I) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (M\<langle>N\<rangle>.P) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (Case C) = \<langle>\<epsilon>, \<bottom>\<rangle>"
| "extractFrame (P \<parallel> Q) = (extractFrame P) \<otimes>\<^sub>F (extractFrame Q)"
| "extractFrame ((\<lbrace>\<Psi>\<rbrace>::('a, 'b, 'c) psi)) = \<langle>\<epsilon>, \<Psi>\<rangle>" 

| "extractFrame (\<lparr>\<nu>x\<rparr>P) = \<lparr>\<nu>x\<rparr>(extractFrame P)"
| "extractFrame (!P) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extractFrame' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extractFrame' (Bind x I) = \<langle>\<epsilon>, \<bottom>\<rangle>" 

| "extractFrame'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
| "extractFrame'' (\<box>\<Phi> \<Rightarrow> P C) = \<langle>\<epsilon>, \<bottom>\<rangle>" 
apply(finite_guess add: fsCompose)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess add: freshBottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: freshBottom)+
apply(rule supports_fresh[of "{}"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess add: freshBottom)+
done

lemmas extractFrameSimps = extractFrame_extractFrame'_extractFrame''.simps

lemma extractFrameEqvt[eqvt]:
  fixes p :: "name prm"
  and   P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"

  shows "p \<bullet> (extractFrame P) = extractFrame (p \<bullet> P)"
  and   "p \<bullet> (extractFrame' I) = extractFrame' (p \<bullet> I)"
  and   "p \<bullet> (extractFrame'' C) = extractFrame'' (p \<bullet> C)"
by(nominal_induct P and I and C avoiding: p rule: psi_input_psiCase.strong_inducts)
   (auto simp add: at_prm_fresh[OF at_name_inst] eqvts permBottom
                  pt_fresh_perm_app[OF pt_name_inst, OF at_name_inst])

lemma insertAssertionFresh[intro]:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b
  and   x :: name

  assumes "x \<sharp> F"
  and     "x \<sharp> \<Psi>"

  shows "x \<sharp> (insertAssertion F \<Psi>)"
using assms
by(nominal_induct F avoiding: x \<Psi> rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma insertAssertionFreshChain[intro]:
  fixes F    :: "'b frame"
  and   \<Psi>    :: 'b
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> xvec \<sharp>* (insertAssertion F \<Psi>)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> Xs \<sharp>* (insertAssertion F \<Psi>)"
by(auto simp add: fresh_star_def)

lemma mergeFrameFresh[intro]:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name

  shows "\<lbrakk>x \<sharp> F; x \<sharp> G\<rbrakk> \<Longrightarrow> x \<sharp> (mergeFrame F G)"
by(nominal_induct F avoiding: x G rule: frame.strong_induct)
  (auto simp add: abs_fresh)

lemma mergeFrameFreshChain[intro]:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "\<lbrakk>xvec \<sharp>* F; xvec \<sharp>* G\<rbrakk> \<Longrightarrow> xvec \<sharp>* (mergeFrame F G)"
  and   "\<lbrakk>Xs \<sharp>* F; Xs \<sharp>* G\<rbrakk> \<Longrightarrow> Xs \<sharp>* (mergeFrame F G)"
by(auto simp add: fresh_star_def)

lemma extractFrameFresh:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"
  and   x :: name

  shows "x \<sharp> P \<Longrightarrow> x \<sharp> extractFrame P"
  and   "x \<sharp> I \<Longrightarrow> x \<sharp> extractFrame' I"
  and   "x \<sharp> C \<Longrightarrow> x \<sharp> extractFrame'' C"
by(nominal_induct P and I and C avoiding: x rule: psi_input_psiCase.strong_inducts)
  (auto simp add: abs_fresh)

lemma extractFrameFreshChain:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"
  and   xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* P \<Longrightarrow> xvec \<sharp>* extractFrame P"
  and   "xvec \<sharp>* I \<Longrightarrow> xvec \<sharp>* extractFrame' I"
  and   "xvec \<sharp>* C \<Longrightarrow> xvec \<sharp>* extractFrame'' C"
  and   "Xs \<sharp>* P \<Longrightarrow> Xs \<sharp>* extractFrame P"
  and   "Xs \<sharp>* I \<Longrightarrow> Xs \<sharp>* extractFrame' I"
  and   "Xs \<sharp>* C \<Longrightarrow> Xs \<sharp>* extractFrame'' C"
by(auto simp add: fresh_star_def intro: extractFrameFresh)


lemma guardedFrameSupp[simp]:
  fixes P :: "('a, 'b, 'c) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"
  and   x :: name 

  shows "guarded P \<Longrightarrow> x \<sharp> (extractFrame P)"
  and   "guarded' I \<Longrightarrow> x \<sharp> (extractFrame' I)"
  and   "guarded'' C \<Longrightarrow> x \<sharp> (extractFrame'' C)"
by(nominal_induct P and I and C arbitrary: x rule: psi_input_psiCase.strong_inducts)
  (auto simp add: frameResChainFresh abs_fresh)

lemma frameResChainFresh': 
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "(xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F)) = (\<forall>x \<in> set xvec. x \<in> set yvec \<or> x \<sharp> F)"
by(simp add: frameResChainFresh fresh_star_def)

lemma frameChainFresh[simp]:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (FAssert \<Psi>) = xvec \<sharp>* \<Psi>"
  and   "Xs \<sharp>* (FAssert \<Psi>) = Xs \<sharp>* \<Psi>"
by(simp add: fresh_star_def)+

lemma frameResChainFresh''[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "xvec \<sharp>* yvec"

  shows "xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>F) = xvec \<sharp>* F"

using assms
by(simp_all add: frameResChainFresh')
  (auto simp add: fresh_star_def fresh_def name_list_supp)

lemma frameResChainFresh'''[simp]:
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"
  
  assumes "x \<sharp> xvec"

  shows "x \<sharp> (\<lparr>\<nu>*xvec\<rparr>F) = x \<sharp> F"
using assms
by(induct xvec) (auto simp add: abs_fresh)

lemma FFreshBottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (\<bottom>\<^sub>F)"
  and   "Xs \<sharp>* (\<bottom>\<^sub>F)"
by(auto simp add: fresh_star_def)

lemma SFreshBottom[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"

  shows "xvec \<sharp>* (SBottom)"
  and   "Xs \<sharp>* (SBottom)"
by(auto simp add: fresh_star_def)
(*
lemma freshChainComp[simp]:
  fixes xvec :: "name list"
  and   Xs   :: "name set"
  and   \<Psi>    :: 'b
  and   \<Psi>'   :: 'b

  shows "xvec \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((xvec \<sharp>* \<Psi>) \<and> xvec \<sharp>* \<Psi>')"
  and   "Xs \<sharp>* (\<Psi> \<otimes> \<Psi>') = ((Xs \<sharp>* \<Psi>) \<and> Xs \<sharp>* \<Psi>')"
by(auto simp add: fresh_star_def)
*)
lemma freshFrameDest[dest]:
  fixes A\<^sub>F    :: "name list"
  and   \<Psi>\<^sub>F   :: 'b
  and   xvec  :: "name list"

  assumes "xvec \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"

  shows "xvec \<sharp>* A\<^sub>F \<Longrightarrow> xvec \<sharp>* \<Psi>\<^sub>F"
  and   "A\<^sub>F \<sharp>* xvec \<Longrightarrow> xvec \<sharp>* \<Psi>\<^sub>F"
proof -
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "xvec \<sharp>* A\<^sub>F"
  ultimately show "xvec \<sharp>* \<Psi>\<^sub>F"
    by(simp add: frameResChainFreshSet) (force simp add: fresh_def name_list_supp fresh_star_def)
next
  from assms have "(set xvec) \<sharp>* (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>)"
    by(simp add: fresh_star_def)
  moreover assume "A\<^sub>F \<sharp>* xvec"
  ultimately show "xvec \<sharp>* \<Psi>\<^sub>F"
    by(simp add: frameResChainFreshSet) (force simp add: fresh_def name_list_supp fresh_star_def)
qed

lemma insertAssertionSimps[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   \<Psi>  :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>"

  shows "insertAssertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<Psi> = \<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms
by(induct A\<^sub>F arbitrary: F) auto

lemma mergeFrameSimps[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   \<Psi>  :: 'b

  assumes "A\<^sub>F \<sharp>* \<Psi>"

  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle> = \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<rangle>"
using assms
by(induct A\<^sub>F arbitrary: F) auto

lemma mergeFrames[simp]:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   A\<^sub>G  :: "name list"
  and   \<Psi>\<^sub>G :: 'b

  assumes "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"

  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>) = (\<langle>(A\<^sub>F@A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
by(induct A\<^sub>F) auto

lemma frameImpResFreshLeft:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F F"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from \<open>A\<^sub>F \<sharp>* (x, \<phi>)\<close> have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with \<open>y \<sharp> F\<close> have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alphaFrameRes)
  with \<open>x \<sharp> F\<close> \<open>y \<sharp> F\<close> have "\<lparr>\<nu>y\<rparr>F \<turnstile>\<^sub>F \<phi>" by simp
  with Feq have "\<langle>(y#A\<^sub>F), \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by simp
  with Feq \<open>A\<^sub>F \<sharp>* \<phi>\<close> \<open>y \<sharp> \<phi>\<close> show "F \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
qed

lemma frameImpResFreshRight:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>F"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from \<open>A\<^sub>F \<sharp>* (x, \<phi>)\<close> have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> \<phi>" and "y \<sharp> F" and "x \<noteq> y"
    by(generate_fresh "name", auto)
  
  assume "F \<turnstile>\<^sub>F \<phi>"
  with Feq \<open>A\<^sub>F \<sharp>* \<phi>\<close> \<open>y \<sharp> \<phi>\<close> have "\<langle>(y#A\<^sub>F), \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  moreover with \<open>y \<sharp> F\<close> \<open>x \<sharp> F\<close> Feq show "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
    by(subst alphaFrameRes) auto
qed

lemma frameResFresh:
  fixes F :: "'b frame"
  and   x :: name
  
  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F F"
using assms
by(auto simp add: FrameStatEq_def intro: frameImpResFreshLeft frameImpResFreshRight)

lemma frameImpResPres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>G"
proof(auto simp add: FrameStatImp_def)
  fix \<phi>::'c
  obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, \<phi>)"
    by(rule freshFrame)
  from \<open>A\<^sub>F \<sharp>* (x, \<phi>)\<close> have "x \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+
  obtain y where "y \<sharp> A\<^sub>F" and "y \<sharp> F" and "y \<sharp> G"
             and "x \<noteq> y" and "y \<sharp> \<phi>"
    by(generate_fresh "name", auto)
  assume "\<lparr>\<nu>x\<rparr>F \<turnstile>\<^sub>F \<phi>"
  with \<open>y \<sharp> F\<close> have "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) \<turnstile>\<^sub>F \<phi>" by(simp add: alphaFrameRes)
  with Feq \<open>x \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F\<close> have "\<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with \<open>y \<sharp> \<phi>\<close> \<open>A\<^sub>F \<sharp>* \<phi>\<close> have "\<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  hence "([(x, y)] \<bullet> \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>) \<turnstile>\<^sub>F ([(x, y)] \<bullet> \<phi>)"
    by(rule frameImpClosed)
  with \<open>x \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F\<close> Feq have "F \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>"
    by(simp add: eqvts)
  with \<open>F \<hookrightarrow>\<^sub>F G\<close> have "G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>" by(simp add: FrameStatImp_def)
  
  obtain A\<^sub>G \<Psi>\<^sub>G where Geq: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* (x, y, \<phi>)"
    by(rule freshFrame)
  from \<open>A\<^sub>G \<sharp>* (x, y, \<phi>)\<close> have "x \<sharp> A\<^sub>G" and "y \<sharp> A\<^sub>G" and "A\<^sub>G \<sharp>* \<phi>" by simp+
  from \<open>G \<turnstile>\<^sub>F [(x, y)] \<bullet> \<phi>\<close> have "([(x, y)] \<bullet> G) \<turnstile>\<^sub>F [(x, y)] \<bullet> [(x, y)] \<bullet> \<phi>"
    by(rule frameImpClosed)
  with Geq \<open>x \<sharp> A\<^sub>G\<close> \<open>y \<sharp> A\<^sub>G\<close> have "\<langle>A\<^sub>G, [(x, y)] \<bullet> \<Psi>\<^sub>G\<rangle> \<turnstile>\<^sub>F \<phi>" by(simp add: eqvts)
  with \<open>y \<sharp> \<phi>\<close> \<open>A\<^sub>G \<sharp>* \<phi>\<close> have "\<langle>(y#A\<^sub>G), [(x, y)] \<bullet> \<Psi>\<^sub>G\<rangle> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI dest: frameImpE simp del: frameResChain.simps)
  with \<open>y \<sharp> G\<close> \<open>x \<sharp> A\<^sub>G\<close> \<open>y \<sharp> A\<^sub>G\<close> Geq show "\<lparr>\<nu>x\<rparr>G \<turnstile>\<^sub>F \<phi>"
    by(subst alphaFrameRes) (fastforce simp add: eqvts)+
qed

lemma frameResPres:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   x :: name
  
  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>x\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>G"
using assms
by(auto simp add: FrameStatEq_def intro: frameImpResPres)

lemma frameImpResComm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
proof(case_tac "x = y")
  assume "x = y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  show ?thesis
  proof(auto simp add: FrameStatImp_def)
    fix \<phi>::'c
    obtain A\<^sub>F \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (x, y, \<phi>)"
      by(rule freshFrame)
    then have "x \<sharp> A\<^sub>F" and "y \<sharp> A\<^sub>F" and "A\<^sub>F \<sharp>* \<phi>" by simp+

    obtain x'::name where "x' \<noteq> x" and "x' \<noteq> y" and "x' \<sharp> F" and "x' \<sharp> \<phi>" and "x' \<sharp> A\<^sub>F"
      by(generate_fresh "name") auto
    obtain y'::name where "y' \<noteq> x" and "y' \<noteq> y" and "y' \<noteq> x'" and "y' \<sharp> F" and "y' \<sharp> \<phi>" and "y' \<sharp> A\<^sub>F"
      by(generate_fresh "name") auto
  
    from \<open>y' \<sharp> F\<close> have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F))"
      by(simp add: alphaFrameRes)
    moreover from \<open>x' \<sharp> F\<close> \<open>x' \<noteq> y\<close> \<open>y' \<noteq> x'\<close> have "\<dots> = \<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> (\<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> F)))"
      by(rule_tac alphaFrameRes) (simp add: abs_fresh fresh_left)
    moreover with  \<open>y' \<noteq> x'\<close> \<open>y' \<noteq> x\<close> have "\<dots> = \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    ultimately have A: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)= \<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*A\<^sub>F\<rparr>(FAssert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F))))"
      using  Feq \<open>x \<sharp> A\<^sub>F\<close> \<open>x' \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F\<close> \<open>y' \<sharp> A\<^sub>F\<close>
      by(simp add: eqvts)

    from \<open>x' \<sharp> F\<close> have "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F))"
      by(simp add: alphaFrameRes)
    moreover from \<open>y' \<sharp> F\<close> \<open>y' \<noteq> x\<close> \<open>y' \<noteq> x'\<close> have "\<dots> = \<lparr>\<nu>y'\<rparr>([(y, y')] \<bullet> (\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> F)))"
      by(rule_tac alphaFrameRes) (simp add: abs_fresh fresh_left)
    moreover with  \<open>y' \<noteq> x'\<close> \<open>x' \<noteq> y\<close> have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(y, y')] \<bullet> [(x, x')] \<bullet> F))"
      by(simp add: eqvts calc_atm)
    moreover with \<open>x' \<noteq> x\<close> \<open>x' \<noteq> y\<close> \<open>y' \<noteq> x\<close> \<open>y' \<noteq> y\<close> \<open>y' \<noteq> x'\<close> \<open>x \<noteq> y\<close>
      have "\<dots> = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>([(x, x')] \<bullet> [(y, y')] \<bullet> F))"
      apply(simp add: eqvts)
      by(subst perm_compose) (simp add: calc_atm)
    ultimately have B: "\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)= \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*A\<^sub>F\<rparr>(FAssert([(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F))))"
      using  Feq \<open>x \<sharp> A\<^sub>F\<close> \<open>x' \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F\<close> \<open>y' \<sharp> A\<^sub>F\<close>
      by(simp add: eqvts)

    from \<open>x' \<sharp> \<phi>\<close> \<open>y' \<sharp> \<phi>\<close> \<open>A\<^sub>F \<sharp>* \<phi>\<close>
    have "\<langle>(x'#y'#A\<^sub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi> = \<langle>(y'#x'#A\<^sub>F), [(x, x')] \<bullet> [(y, y')] \<bullet> \<Psi>\<^sub>F\<rangle> \<turnstile>\<^sub>F \<phi>"
      by(force dest: frameImpE intro: frameImpI simp del: frameResChain.simps)
    with A B have "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi> = (\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
      by simp
    moreover assume "(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F)) \<turnstile>\<^sub>F \<phi>"
    ultimately show "(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)) \<turnstile>\<^sub>F \<phi>" by simp
  qed
qed

lemma frameResComm:
  fixes x :: name
  and   y :: name
  and   F :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(auto simp add: FrameStatEq_def intro: frameImpResComm)

lemma frameImpResCommLeft':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frameImpResComm FrameStatImpTrans frameImpResPres)

lemma frameImpResCommRight':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameImpResComm FrameStatImpTrans frameImpResPres)

lemma frameResComm':
  fixes x    :: name
  and   xvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>F)"
by(induct xvec) (auto intro: frameResComm FrameStatEqTrans frameResPres)

lemma frameImpChainComm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameImpResCommLeft' FrameStatImpTrans frameImpResPres)

lemma frameResChainComm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   F    :: "'b frame"

  shows "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>F) \<simeq>\<^sub>F \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>*xvec\<rparr>F)"
by(induct xvec) (auto intro: frameResComm' FrameStatEqTrans frameResPres)

lemma frameImpNilStatEq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<hookrightarrow> \<Psi>')"
by(simp add: FrameStatImp_def AssertionStatImp_def FrameImp_def)


lemma frameNilStatEq[simp]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "(\<langle>\<epsilon>, \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>'\<rangle>) = (\<Psi> \<simeq> \<Psi>')"
by(simp add: FrameStatEq_def AssertionStatEq_def FrameImp_def)

lemma extractFrameChainStatImp:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) (auto intro: frameImpResPres)

lemma extractFrameChainStatEq:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) (auto intro: frameResPres)

lemma insertAssertionExtractFrameFreshImp:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frameImpResPres)

lemma insertAssertionExtractFrameFresh:
  fixes xvec :: "name list"
  and   \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion(extractFrame(\<lparr>\<nu>*xvec\<rparr>P)) \<Psi> \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>(insertAssertion (extractFrame P) \<Psi>)"
using assms
by(induct xvec) (auto intro: frameResPres)

lemma frameImpResChainPres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<hookrightarrow>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<hookrightarrow>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frameImpResPres)

lemma frameResChainPres:
  fixes F    :: "'b frame"
  and   G    :: "'b frame"
  and   xvec :: "name list"

  assumes "F \<simeq>\<^sub>F G"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F \<lparr>\<nu>*xvec\<rparr>G"
using assms
by(induct xvec) (auto intro: frameResPres)

lemma insertAssertionE:
  fixes F  :: "('b::fs_name) frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"

  assumes "insertAssertion F \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>"
  and     "A\<^sub>F \<sharp>* F"
  and     "A\<^sub>F \<sharp>* \<Psi>"
  and     "distinct A\<^sub>F"

  obtains \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "\<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F"
proof -
  assume A: "\<And>\<Psi>\<^sub>F. \<lbrakk>F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>\<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F"
  proof(nominal_induct F avoiding: \<Psi> A\<^sub>F \<Psi>' rule: frame.strong_induct)
    case(FAssert \<Psi> A\<^sub>F \<Psi>')
    thus ?case by auto
  next
    case(FRes x F \<Psi> A\<^sub>F \<Psi>')
    from \<open>insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>\<close> \<open>x \<sharp> \<Psi>\<close>
    obtain y A\<^sub>F' where "A\<^sub>F = y#A\<^sub>F'" by(induct A\<^sub>F) auto
    with \<open>insertAssertion (\<lparr>\<nu>x\<rparr>F) \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> A\<^sub>F\<close>
    have A: "insertAssertion F \<Psi> = \<langle>([(x, y)] \<bullet> A\<^sub>F'), [(x, y)] \<bullet> \<Psi>'\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    from \<open>A\<^sub>F = y#A\<^sub>F'\<close> \<open>A\<^sub>F \<sharp>* \<Psi>\<close> have "y \<sharp> \<Psi>" and "A\<^sub>F' \<sharp>* \<Psi>" by simp+
    from \<open>distinct A\<^sub>F\<close> \<open>A\<^sub>F = y#A\<^sub>F'\<close> have "y \<sharp> A\<^sub>F'" and "distinct A\<^sub>F'" by auto
    from \<open>A\<^sub>F \<sharp>* (\<lparr>\<nu>x\<rparr>F)\<close> \<open>x \<sharp> A\<^sub>F\<close> \<open>A\<^sub>F = y#A\<^sub>F'\<close> have "y \<sharp> F" and "A\<^sub>F' \<sharp>* F" and "x \<sharp> A\<^sub>F'"
      apply -
      apply(auto simp add: abs_fresh)
      apply(hypsubst_thin)
      apply(subst fresh_star_def)
      apply(erule rev_mp)
      apply(subst fresh_star_def)
      apply(clarify)
      apply(erule_tac x=xa in ballE)
      apply(simp add: abs_fresh)
      apply auto
      by(simp add: fresh_def name_list_supp)
    with \<open>x \<sharp> A\<^sub>F'\<close> \<open>y \<sharp> A\<^sub>F'\<close> have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* F" by simp
    from \<open>A\<^sub>F' \<sharp>* \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>F') \<sharp>* \<Psi>" by simp
    with \<open>\<And>\<Psi> A\<^sub>F \<Psi>'. \<lbrakk>insertAssertion F \<Psi> = \<langle>A\<^sub>F, \<Psi>'\<rangle>; A\<^sub>F \<sharp>* F; A\<^sub>F \<sharp>* \<Psi>; distinct A\<^sub>F\<rbrakk> \<Longrightarrow> \<exists>\<Psi>\<^sub>F. F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> \<Psi>' = \<Psi> \<otimes> \<Psi>\<^sub>F\<close> A 
         \<open>([(x, y)] \<bullet> A\<^sub>F') \<sharp>* F\<close> \<open>distinct A\<^sub>F'\<close> \<open>x \<sharp> A\<^sub>F'\<close> \<open>y \<sharp> A\<^sub>F'\<close>
    obtain \<Psi>\<^sub>F where Feq: "F = \<langle>A\<^sub>F', \<Psi>\<^sub>F\<rangle>" and \<Psi>eq: "([(x, y)] \<bullet> \<Psi>') = \<Psi> \<otimes> \<Psi>\<^sub>F"
      by force
    
    from Feq have "\<lparr>\<nu>x\<rparr>F =  \<langle>(x#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
    hence "([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>F) = [(x, y)] \<bullet> \<langle>(x#A\<^sub>F'), \<Psi>\<^sub>F\<rangle>" by simp
    hence "\<lparr>\<nu>x\<rparr>F = \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" using \<open>y \<sharp> F\<close> \<open>A\<^sub>F = y#A\<^sub>F'\<close> \<open>x \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F'\<close>
      by(simp add: eqvts calc_atm alphaFrameRes)

    moreover from \<Psi>eq have "[(x, y)] \<bullet> ([(x, y)] \<bullet> \<Psi>') = [(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>F)"
      by simp
    with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi>' = \<Psi> \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by(simp add: eqvts)
    ultimately show ?case
      by blast
  qed
  with A show ?thesis
    by blast
qed

lemma mergeFrameE:
  fixes F   :: "'b frame"
  and   G   :: "'b frame"
  and   A\<^sub>F\<^sub>G :: "name list"
  and   \<Psi>\<^sub>F\<^sub>G :: 'b

  assumes "mergeFrame F G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>"
  and     "distinct A\<^sub>F\<^sub>G"
  and     "A\<^sub>F\<^sub>G \<sharp>* F"
  and     "A\<^sub>F\<^sub>G \<sharp>* G"

  obtains A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G where "A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G" and "\<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" and "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
proof -
  assume A: "\<And>A\<^sub>F A\<^sub>G \<Psi>\<^sub>F \<Psi>\<^sub>G. \<lbrakk>A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G; \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G; F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>; G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>; A\<^sub>F \<sharp>* \<Psi>\<^sub>G; A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<rbrakk> \<Longrightarrow> thesis"
  from assms have "\<exists>A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G. A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G \<and> \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G \<and> F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle> \<and> A\<^sub>F \<sharp>* \<Psi>\<^sub>G \<and> A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  proof(nominal_induct F avoiding: G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G rule: frame.strong_induct)
    case(FAssert \<Psi> G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G)
    thus ?case
      apply auto
      apply(rule_tac x="[]" in exI) 
      by(drule_tac insertAssertionE) auto
  next
    case(FRes x F G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G)
    from \<open>mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>\<close> \<open>x \<sharp> G\<close>
    obtain y A\<^sub>F\<^sub>G' where "A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'" by(induct A\<^sub>F\<^sub>G) auto
    with \<open>A\<^sub>F\<^sub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)\<close> \<open>x \<sharp> A\<^sub>F\<^sub>G\<close> have "A\<^sub>F\<^sub>G' \<sharp>* F" and "x \<sharp> A\<^sub>F\<^sub>G'"
      by(auto simp add: supp_list_cons fresh_star_def fresh_def name_list_supp abs_supp frame.supp)
    from \<open>A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'\<close> \<open>A\<^sub>F\<^sub>G \<sharp>* G\<close> have "y \<sharp> G" and "A\<^sub>F\<^sub>G' \<sharp>* G" by simp+
    from \<open>A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'\<close> \<open>A\<^sub>F\<^sub>G \<sharp>* (\<lparr>\<nu>x\<rparr>F)\<close> \<open>x \<sharp> A\<^sub>F\<^sub>G\<close> have "y \<sharp> F" and "A\<^sub>F\<^sub>G' \<sharp>* F"
      apply(auto simp add: abs_fresh frameResChainFreshSet)
      apply(hypsubst_thin)
      by(induct A\<^sub>F\<^sub>G') (auto simp add: abs_fresh)
    from \<open>distinct A\<^sub>F\<^sub>G\<close> \<open>A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'\<close> have "y \<sharp> A\<^sub>F\<^sub>G'" and "distinct A\<^sub>F\<^sub>G'" by auto
    
    with \<open>A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'\<close> \<open>mergeFrame (\<lparr>\<nu>x\<rparr>F) G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>\<close> \<open>x \<sharp> G\<close> \<open>x \<sharp> A\<^sub>F\<^sub>G\<close> \<open>y \<sharp> A\<^sub>F\<^sub>G'\<close>
    have "mergeFrame F G = \<langle>A\<^sub>F\<^sub>G', [(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G\<rangle>"
      by(simp add: frame.inject alpha eqvts)
    with \<open>distinct A\<^sub>F\<^sub>G'\<close> \<open>A\<^sub>F\<^sub>G' \<sharp>* F\<close> \<open>A\<^sub>F\<^sub>G' \<sharp>* G\<close>
         \<open>\<And>G A\<^sub>F\<^sub>G \<Psi>\<^sub>F\<^sub>G. \<lbrakk>mergeFrame F G = \<langle>A\<^sub>F\<^sub>G, \<Psi>\<^sub>F\<^sub>G\<rangle>; distinct A\<^sub>F\<^sub>G; A\<^sub>F\<^sub>G \<sharp>* F; A\<^sub>F\<^sub>G \<sharp>* G\<rbrakk> \<Longrightarrow> \<exists>A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G. A\<^sub>F\<^sub>G = A\<^sub>F@A\<^sub>G \<and> \<Psi>\<^sub>F\<^sub>G = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G \<and> F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle> \<and> G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle> \<and> A\<^sub>F \<sharp>* \<Psi>\<^sub>G \<and> A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<close>
    obtain A\<^sub>F \<Psi>\<^sub>F A\<^sub>G \<Psi>\<^sub>G where "A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G" and "([(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" and FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
      by metis

    from \<open>A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G\<close> \<open>A\<^sub>F\<^sub>G = y#A\<^sub>F\<^sub>G'\<close> have  "A\<^sub>F\<^sub>G = (y#A\<^sub>F)@A\<^sub>G" by simp
    moreover from \<open>A\<^sub>F\<^sub>G' = A\<^sub>F@A\<^sub>G\<close> \<open>y \<sharp> A\<^sub>F\<^sub>G'\<close> \<open>x \<sharp> A\<^sub>F\<^sub>G'\<close> have "x \<sharp> A\<^sub>F" and "y \<sharp> A\<^sub>F" and "x \<sharp> A\<^sub>G" and "y \<sharp> A\<^sub>G" by simp+
    with \<open>y \<sharp> G\<close> \<open>x \<sharp> G\<close> \<open>x \<sharp> A\<^sub>F\<^sub>G\<close> FrG have "y \<sharp> \<Psi>\<^sub>G" and "x \<sharp> \<Psi>\<^sub>G" 
      by auto
    from \<open>([(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<close> have "([(x, y)] \<bullet> [(x, y)] \<bullet> \<Psi>\<^sub>F\<^sub>G) = [(x, y)] \<bullet> (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G)"
      by simp
    with \<open>x \<sharp> \<Psi>\<^sub>G\<close> \<open>y \<sharp> \<Psi>\<^sub>G\<close> have "\<Psi>\<^sub>F\<^sub>G = ([(x, y)] \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>G" by(simp add: eqvts)
    moreover from FrF have "([(x, y)] \<bullet> F) = [(x, y)] \<bullet> \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" by simp
    with \<open>x \<sharp> A\<^sub>F\<close> \<open>y \<sharp> A\<^sub>F\<close> have "([(x, y)] \<bullet> F) = \<langle>A\<^sub>F, [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: eqvts)
    hence "\<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> F) = \<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: frame.inject)
    with \<open>y \<sharp> F\<close> have "\<lparr>\<nu>x\<rparr>F = \<langle>(y#A\<^sub>F), [(x, y)] \<bullet> \<Psi>\<^sub>F\<rangle>" by(simp add: alphaFrameRes)
    moreover with \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<close> have "([(x, y)] \<bullet> A\<^sub>G) \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>x \<sharp> A\<^sub>G\<close> \<open>y \<sharp> A\<^sub>G\<close> have "A\<^sub>G \<sharp>* ([(x, y)] \<bullet> \<Psi>\<^sub>F)" by simp
    moreover from \<open>A\<^sub>F \<sharp>* \<Psi>\<^sub>G\<close> \<open>y \<sharp> \<Psi>\<^sub>G\<close> have "(y#A\<^sub>F) \<sharp>* \<Psi>\<^sub>G" by simp
    ultimately show ?case using FrG 
      by blast
  qed
  with A show ?thesis by blast
qed

lemma mergeFrameRes1[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   x   :: name
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<Psi>\<^sub>F"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  
  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>)) = (\<langle>(A\<^sub>F@x#A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
apply(fold frameResChain.simps)
by(rule mergeFrames) auto

lemma mergeFrameRes2[simp]:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b
  and   x   :: name
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b
  
  assumes "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* A\<^sub>F"
  and     "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<Psi>\<^sub>F"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  
  shows "(\<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>) \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>(\<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>)) = (\<langle>(A\<^sub>F@x#A\<^sub>G), \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>)"
using assms
apply(fold frameResChain.simps)
by(rule mergeFrames) auto

lemma insertAssertionResChain[simp]:
  fixes xvec :: "name list"
  and   F    :: "'b frame"
  and   \<Psi>   :: 'b

  assumes "xvec \<sharp>* \<Psi>"

  shows "insertAssertion (\<lparr>\<nu>*xvec\<rparr>F) \<Psi> = \<lparr>\<nu>*xvec\<rparr>(insertAssertion F \<Psi>)"
using assms
by(induct xvec) auto

lemma extractFrameResChain[simp]:
  fixes xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  shows "extractFrame(\<lparr>\<nu>*xvec\<rparr>P) = \<lparr>\<nu>*xvec\<rparr>(extractFrame P)"
by(induct xvec) auto

lemma frameResFreshChain:
  fixes xvec :: "name list"
  and   F    :: "'b frame"

  assumes "xvec \<sharp>* F"

  shows "\<lparr>\<nu>*xvec\<rparr>F \<simeq>\<^sub>F F"
using assms
proof(induct xvec)
  case Nil
  thus ?case by simp
next
  case(Cons x xvec)
  thus ?case
    by auto (metis frameResPres frameResFresh FrameStatEqTrans)
qed

end

locale assertion = assertionAux SCompose SImp SBottom SChanEq
  for SCompose  :: "'b::fs_name \<Rightarrow> 'b \<Rightarrow> 'b"
  and SImp      :: "'b \<Rightarrow> 'c::fs_name \<Rightarrow> bool"
  and SBottom   :: 'b
  and SChanEq   :: "'a::fs_name \<Rightarrow> 'a \<Rightarrow> 'c" +

  assumes chanEqSym:     "SImp \<Psi> (SChanEq M N) \<Longrightarrow> SImp \<Psi> (SChanEq N M)"
  and     chanEqTrans:   "\<lbrakk>SImp \<Psi> (SChanEq M N); SImp \<Psi> (SChanEq N L)\<rbrakk> \<Longrightarrow> SImp \<Psi> (SChanEq M L)"
  and     Composition:   "assertionAux.AssertionStatEq SImp \<Psi> \<Psi>' \<Longrightarrow> assertionAux.AssertionStatEq SImp (SCompose \<Psi> \<Psi>'') (SCompose \<Psi>' \<Psi>'')"
  and     Identity:      "assertionAux.AssertionStatEq SImp (SCompose \<Psi> SBottom) \<Psi>"
  and     Associativity: "assertionAux.AssertionStatEq SImp (SCompose (SCompose \<Psi> \<Psi>') \<Psi>'') (SCompose \<Psi> (SCompose \<Psi>' \<Psi>''))"
  and     Commutativity: "assertionAux.AssertionStatEq SImp (SCompose \<Psi> \<Psi>') (SCompose \<Psi>' \<Psi>)"

begin

notation SCompose (infixr "\<otimes>" 90)
notation SImp ("_ \<turnstile> _" [85, 85] 85)
notation SChanEq ("_ \<leftrightarrow> _" [90, 90] 90)
notation SBottom ("\<bottom>" 90)

lemma compositionSym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi>'' \<otimes> \<Psi>'"
proof -
  have "\<Psi>'' \<otimes> \<Psi> \<simeq> \<Psi> \<otimes> \<Psi>''" by(rule Commutativity)
  moreover from assms have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
  moreover have "\<Psi>' \<otimes> \<Psi>'' \<simeq> \<Psi>'' \<otimes> \<Psi>'" by(rule Commutativity)
  ultimately show ?thesis by(blast intro: AssertionStatEqTrans)
qed

lemma Composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"
  and     "\<Psi>'' \<simeq> \<Psi>'''"
  
  shows "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>'''"
using assms
by(metis Composition Commutativity AssertionStatEqTrans)
  

lemma composition':
  fixes \<Psi>    :: 'b
  and   \<Psi>'   :: 'b
  and   \<Psi>''  :: 'b
  and   \<Psi>''' :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
proof -
  have "(\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>''' \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Associativity)
  moreover from assms have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> \<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''')"
    by(rule Composition)
  moreover have "\<Psi>' \<otimes> (\<Psi>'' \<otimes> \<Psi>''') \<simeq> (\<Psi>' \<otimes> \<Psi>'') \<otimes> \<Psi>'''"
    by(rule Associativity[THEN AssertionStatEqSym])
  ultimately show ?thesis by(blast dest: AssertionStatEqTrans)
qed

lemma associativitySym:
  fixes \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b
  
  shows "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
proof -
  have "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')"
    by(rule Associativity)
  moreover have "\<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>')"
    by(rule compositionSym[OF Commutativity])
  moreover have "\<Psi> \<otimes> (\<Psi>'' \<otimes> \<Psi>') \<simeq> (\<Psi> \<otimes> \<Psi>'') \<otimes> \<Psi>'"
    by(rule AssertionStatEqSym[OF Associativity])
  ultimately show ?thesis
    by(blast dest: AssertionStatEqTrans)
qed
(*
lemma frameChanEqSym:
  fixes F :: "'b frame"
  and   M :: 'a
  and   N :: 'a

  assumes "F \<turnstile>\<^sub>F M \<leftrightarrow> N"
  
  shows "F \<turnstile>\<^sub>F N \<leftrightarrow> M"
using assms
apply(auto simp add: FrameImp_def)
by(force intro: chanEqSym simp add: FrameImp_def)

lemma frameChanEqTrans:
  fixes F :: "'b frame"
  and   M :: 'a
  and   N :: 'a

  assumes "F \<turnstile>\<^sub>F M \<leftrightarrow> N"
  and     "F \<turnstile>\<^sub>F N \<leftrightarrow> L"
  
  shows "F \<turnstile>\<^sub>F M \<leftrightarrow> L"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* (M, N, L)"
    by(rule freshFrame)
  with assms show ?thesis
    by(force dest: frameImpE intro: frameImpI chanEqTrans)
qed
*)
lemma frameIntAssociativity:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b
  and   \<Psi>'' :: 'b

  shows "\<langle>A\<^sub>F, (\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi> \<otimes> (\<Psi>' \<otimes> \<Psi>'')\<rangle>"
by(induct A\<^sub>F) (auto intro: Associativity frameResPres)

lemma frameIntCommutativity:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>   :: 'b
  and   \<Psi>'  :: 'b

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<rangle>"
by(induct A\<^sub>F) (auto intro: Commutativity frameResPres)

lemma frameIntIdentity:
  fixes A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b 

  shows "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> SBottom\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
by(induct A\<^sub>F) (auto intro: Identity frameResPres)

lemma frameIntComposition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms
by(induct A\<^sub>F) (auto intro: Composition frameResPres)

lemma frameIntCompositionSym:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>'\<rangle>"
using assms
by(induct A\<^sub>F) (auto intro: compositionSym frameResPres)

lemma frameCommutativity:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<otimes>\<^sub>F G \<simeq>\<^sub>F G \<otimes>\<^sub>F F"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* G"
    by(rule freshFrame)
  moreover obtain A\<^sub>G \<Psi>\<^sub>G where "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F" and "A\<^sub>G \<sharp>* A\<^sub>F"
    by(rule_tac C="(A\<^sub>F, \<Psi>\<^sub>F)" in freshFrame) auto
  moreover from \<open>A\<^sub>F \<sharp>* G\<close> \<open>G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>\<close> \<open>A\<^sub>G \<sharp>* A\<^sub>F\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
    by auto
  ultimately show ?thesis
    by auto (metis FrameStatEqTrans frameChainAppend frameResChainComm frameIntCommutativity)
qed
  
lemma frameScopeExt:
  fixes x :: name
  and   F :: "'b frame"
  and   G :: "'b frame"

  assumes "x \<sharp> F"

  shows "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
proof -
  have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F \<lparr>\<nu>x\<rparr>(G \<otimes>\<^sub>F F)"
    by(metis frameResPres frameCommutativity)
  with \<open>x \<sharp> F\<close> have "\<lparr>\<nu>x\<rparr>(F \<otimes>\<^sub>F G) \<simeq>\<^sub>F (\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F"
    by simp
  moreover have "(\<lparr>\<nu>x\<rparr>G) \<otimes>\<^sub>F F \<simeq>\<^sub>F F \<otimes>\<^sub>F (\<lparr>\<nu>x\<rparr>G)"
    by(rule frameCommutativity)
  ultimately show ?thesis by(rule FrameStatEqTrans)
qed

lemma insertDoubleAssertionStatEq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "insertAssertion(insertAssertion F \<Psi>) \<Psi>' \<simeq>\<^sub>F (insertAssertion F) (\<Psi> \<otimes> \<Psi>')"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'" and "A\<^sub>F \<sharp>* (\<Psi> \<otimes> \<Psi>')"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  thus ?thesis
    by auto (metis frameIntComposition Commutativity frameIntAssociativity FrameStatEqTrans FrameStatEqSym)
qed

lemma guardedStatEq:
  fixes P  :: "('a, 'b, 'c) psi"
  and   I  :: "('a, 'b, 'c) input"
  and   C  :: "('a, 'b, 'c) psiCase"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b

  shows "\<lbrakk>guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
  and   "\<lbrakk>guarded' I; extractFrame' I = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
  and   "\<lbrakk>guarded'' C; extractFrame'' C = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> supp \<Psi>\<^sub>P = ({}::name set)"
proof(nominal_induct P and I and C arbitrary: A\<^sub>P \<Psi>\<^sub>P rule: psi_input_psiCase.strong_inducts)
  case(PsiNil A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Output M N P A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Input M In  A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Case psiCase A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Par P Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q)
  from \<open>guarded(P \<parallel> Q)\<close> have "guarded P" and "guarded Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* Q" by(rule freshFrame)
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" 
    by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P)" in freshFrame) auto
  
  from \<open>\<And>A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>P = ({}::name set))\<close> \<open>guarded P\<close> FrP
  have "\<Psi>\<^sub>P \<simeq> \<bottom>" and "supp \<Psi>\<^sub>P = ({}::name set)" by simp+
  from \<open>\<And>A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>guarded Q; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>Q \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>Q = ({}::name set))\<close> \<open>guarded Q\<close> FrQ
  have "\<Psi>\<^sub>Q \<simeq> \<bottom>" and "supp \<Psi>\<^sub>Q = ({}::name set)" by simp+
  
  from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extractFrameFreshChain) auto
  with \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> FrP FrQ \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by auto
  with \<open>supp \<Psi>\<^sub>P = {}\<close> \<open>supp \<Psi>\<^sub>Q = {}\<close> compSupp have "\<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q"
    by blast
  moreover from \<open>\<Psi>\<^sub>P \<simeq> \<bottom>\<close> \<open>\<Psi>\<^sub>Q \<simeq> \<bottom>\<close> have "\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<simeq> \<bottom>"
    by(metis Composition Identity Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using \<open>supp \<Psi>\<^sub>P = {}\<close> \<open>supp \<Psi>\<^sub>Q = {}\<close> compSupp
    by blast
next
  case(Res x P A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P)
  from \<open>guarded(\<lparr>\<nu>x\<rparr>P)\<close> have "guarded P" by simp
  moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(rule freshFrame)
  moreover note \<open>\<And>A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<rbrakk> \<Longrightarrow> \<Psi>\<^sub>P \<simeq> \<bottom> \<and> (supp \<Psi>\<^sub>P = ({}::name set))\<close>
  ultimately have "\<Psi>\<^sub>P \<simeq> \<bottom>" and "supp \<Psi>\<^sub>P = ({}::name set)" by auto
  from FrP \<open>extractFrame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>\<close> have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>" by simp
  with \<open>supp \<Psi>\<^sub>P = {}\<close> have "\<Psi>\<^sub>P = \<Psi>\<^sub>x\<^sub>P" by(auto simp del: frameResChain.simps)
  with \<open>\<Psi>\<^sub>P \<simeq> \<bottom>\<close> \<open>supp \<Psi>\<^sub>P = {}\<close> show ?case
    by simp
next
  case(Assert \<Psi> A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Bang P A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by simp
next
  case(Trm M P)
  thus ?case by simp
next
  case(Bind x I)
  thus ?case by simp
next
  case EmptyCase
  thus ?case by simp
next
  case(Cond \<phi> P psiCase)
  thus ?case by simp
qed

end

end
