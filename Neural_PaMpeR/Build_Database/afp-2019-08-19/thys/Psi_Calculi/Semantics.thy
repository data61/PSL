(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Semantics
  imports Frame
begin

nominal_datatype ('a, 'b, 'c) boundOutput = 
  BOut "'a::fs_name" "('a, 'b::fs_name, 'c::fs_name) psi" ("_ \<prec>' _" [110, 110] 110)
| BStep "\<guillemotleft>name\<guillemotright> ('a, 'b, 'c) boundOutput"                ("\<lparr>\<nu>_\<rparr>_" [110, 110] 110)

primrec BOresChain :: "name list \<Rightarrow> ('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput \<Rightarrow> 
                      ('a, 'b, 'c) boundOutput" where
  Base: "BOresChain [] B = B"
| Step: "BOresChain (x#xs) B = \<lparr>\<nu>x\<rparr>(BOresChain xs B)"

abbreviation
  BOresChainJudge ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80) where "\<lparr>\<nu>*xvec\<rparr>B \<equiv> BOresChain xvec B"

lemma BOresChainEqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>B) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> B)"
by(induct_tac xvec, auto)

lemma BOresChainSimps[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   N'   :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   B'    :: "('a, 'b, 'c) boundOutput"

  shows "(\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = N' \<prec>' P') = (xvec = [] \<and> N = N' \<and> P = P')"
  and   "(N' \<prec>' P' = \<lparr>\<nu>*xvec\<rparr>N \<prec>' P) = (xvec = [] \<and> N = N' \<and> P = P')"
  and   "(N' \<prec>' P' = N \<prec>' P) = (N = N' \<and> P = P')"
  and   "(\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*xvec\<rparr>B') = (B = B')"
by(induct xvec) (auto simp add: boundOutput.inject alpha)

lemma outputFresh[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(Xs \<sharp>* (N \<prec>' P)) = ((Xs \<sharp>* N) \<and> (Xs \<sharp>* P))"
  and   "(xvec \<sharp>* (N \<prec>' P)) = ((xvec \<sharp>* N) \<and> (xvec \<sharp>* P))"
by(auto simp add: fresh_star_def)

lemma boundOutputFresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   B   :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"

  shows "(x \<sharp> (\<lparr>\<nu>*xvec\<rparr>B)) = (x \<in> set xvec \<or> x \<sharp> B)"
by (induct xvec) (simp_all add: abs_fresh)

lemma boundOutputFreshSet: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"
  and   x    :: name

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> B)"
  and   "yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = (\<forall>x\<in>(set yvec). x \<in> set xvec \<or> x \<sharp> B)"
  and   "Xs \<sharp>* (\<lparr>\<nu>x\<rparr>B) = Xs \<sharp>* [x].B"
  and   "xvec \<sharp>* (\<lparr>\<nu>x\<rparr>B) = xvec \<sharp>* [x].B"
by(simp add: fresh_star_def boundOutputFresh)+

lemma BOresChainSupp:
  fixes xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"

  shows "(supp(\<lparr>\<nu>*xvec\<rparr>B)::name set) = (supp B) - (supp xvec)" 
by(induct xvec)
  (auto simp add: boundOutput.supp supp_list_nil supp_list_cons abs_supp supp_atm)

lemma boundOutputFreshSimps[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"
  and   x    :: name

  shows "Xs \<sharp>* xvec \<Longrightarrow> (Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B)) = (Xs \<sharp>* B)"
  and   "yvec \<sharp>* xvec \<Longrightarrow> yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B) = yvec \<sharp>* B"
  and   "xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>B)"
  and   "x \<sharp> xvec \<Longrightarrow> x \<sharp> \<lparr>\<nu>*xvec\<rparr>B = x \<sharp> B"
apply(simp add: boundOutputFreshSet) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: boundOutputFreshSet) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: boundOutputFreshSet)  
by(simp add: BOresChainSupp fresh_def)

lemma boundOutputChainAlpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"

  assumes xvecFreshB: "(p \<bullet> xvec) \<sharp>* B"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "(set xvec) \<subseteq> (set yvec)"

  shows "(\<lparr>\<nu>*yvec\<rparr>B) = (\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(p \<bullet> B))"
proof -
  note pt_name_inst at_name_inst S
  moreover from \<open>(set xvec) \<subseteq> (set yvec)\<close> have "set xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>B)"
    by(force simp add: boundOutputFreshSet)
  moreover from xvecFreshB \<open>(set xvec) \<subseteq> (set yvec)\<close> have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*yvec\<rparr>B)"
    by (simp add: boundOutputFreshSet) (simp add: fresh_star_def)
  ultimately have "(\<lparr>\<nu>*yvec\<rparr>B) = p \<bullet> (\<lparr>\<nu>*yvec\<rparr>B)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma boundOutputChainAlpha':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes xvecFreshB: "xvec \<sharp>* B"
  and     S: "set p \<subseteq> set xvec \<times> set yvec"
  and     "yvec \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)"

  shows "(\<lparr>\<nu>*zvec\<rparr>B) = (\<lparr>\<nu>*(p \<bullet> zvec)\<rparr>(p \<bullet> B))"
proof -
  note pt_name_inst at_name_inst S \<open>yvec \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)\<close>
  moreover from xvecFreshB have "set (xvec) \<sharp>* (\<lparr>\<nu>*zvec\<rparr>B)"
    by (simp add: boundOutputFreshSet) (simp add: fresh_star_def)
  ultimately have "(\<lparr>\<nu>*zvec\<rparr>B) = p \<bullet> (\<lparr>\<nu>*zvec\<rparr>B)"
    by (rule_tac pt_freshs_freshs [symmetric]) auto
  then show ?thesis by(simp add: eqvts)
qed

lemma boundOutputChainAlpha'':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"

  assumes "(p \<bullet> xvec) \<sharp>* M"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and      "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "(set xvec) \<subseteq> (set yvec)"

  shows "(\<lparr>\<nu>*yvec\<rparr>M \<prec>' P) = (\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(p \<bullet> M) \<prec>' (p \<bullet> P))"
using assms
by(subst boundOutputChainAlpha) auto

lemma boundOutputChainSwap:
  fixes x    :: name
  and   y    :: name
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec :: "name list"

  assumes "y \<sharp> N"
  and     "y \<sharp> P"
  and     "x \<in> (set xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> xvec)\<rparr>([(x ,y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> P)"
proof(case_tac "x=y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with assms show ?thesis
    by(rule_tac xvec="[x]" in boundOutputChainAlpha'') (auto simp add: calc_atm)
qed

lemma alphaBoundOutput:
  fixes x  :: name
  and   y  :: name
  and   B  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"

  assumes "y \<sharp> B"

  shows "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> B)"
using assms
by(auto simp add: boundOutput.inject alpha fresh_left calc_atm)

lemma boundOutputEqFresh:
  fixes B :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   C :: "('a, 'b, 'c) boundOutput"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>C"
  and     "x \<sharp> B"
  
  shows "y \<sharp> C"
using assms
by(auto simp add: boundOutput.inject alpha fresh_left calc_atm)  

lemma boundOutputEqSupp:
  fixes B :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   C :: "('a, 'b, 'c) boundOutput"
  and   x :: name
  and   y :: name

  assumes "\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>y\<rparr>C"
  and     "x \<in> supp B"
  
  shows "y \<in> supp C"
using assms
apply(auto simp add: boundOutput.inject alpha fresh_left calc_atm)
apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
by(simp add: eqvts calc_atm)

lemma boundOutputChainEq:
  fixes xvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"
  and   B'   :: "('a, 'b, 'c) boundOutput"

  assumes "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'"
  and     "xvec \<sharp>* yvec"
  and     "length xvec = length yvec"

  shows "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  B = p \<bullet> B' \<and> (set (map fst p)) \<subseteq> (supp B) \<and> xvec \<sharp>* B' \<and> yvec \<sharp>* B"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec B B')
    case(0 xvec yvec B B')
    have Eq: "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with \<open>length xvec = length yvec\<close> have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec B B')
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>B'\<close> \<open>xvec = x # xvec'\<close> \<open>length xvec = length yvec\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>B = \<lparr>\<nu>*(y#yvec')\<rparr>B'"
      and "yvec = y#yvec'" and "length xvec' = length yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>B) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>B')"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    have IH: "\<And>xvec yvec B B'. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>(B::('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput) = \<lparr>\<nu>*yvec\<rparr>B'; xvec \<sharp>* yvec; length xvec = length yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  B = p \<bullet> B' \<and> set(map fst p) \<subseteq> supp B \<and> xvec \<sharp>* B' \<and> yvec \<sharp>* B"
      by fact
    from EQ \<open>x \<noteq> y\<close> have EQ': "\<lparr>\<nu>*xvec'\<rparr>B = ([(x, y)] \<bullet> (\<lparr>\<nu>*yvec'\<rparr>B'))" 
                     and xFreshB': "x \<sharp> (\<lparr>\<nu>*yvec'\<rparr>B')"
                     and yFreshB: "y \<sharp> (\<lparr>\<nu>*xvec'\<rparr>B)"
      by(metis boundOutput.inject alpha)+
    from xFreshB' \<open>x \<sharp> yvec'\<close> have "x \<sharp> B'"
      by(auto simp add: boundOutputFresh) (simp add: fresh_def name_list_supp)+
    from yFreshB \<open>y \<sharp> xvec'\<close> have "y \<sharp> B"
      by(auto simp add: boundOutputFresh) (simp add: fresh_def name_list_supp)+
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B")
      assume xFreshB: "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B"
      with EQ have yFreshB': "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>B'"
        by(rule boundOutputEqFresh)
      with xFreshB' EQ' have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>B'" 
        by(simp)
      with \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = length yvec'\<close> \<open>length xvec' = n\<close> IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "B = p \<bullet> B'"
                 and "set(map fst p) \<subseteq> supp B" and "xvec' \<sharp>* B'"  and "yvec' \<sharp>* B"
        by blast
      from S have "(set p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover note \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>distinctPerm p\<close> \<open>B = p \<bullet> B'\<close>
                    \<open>xvec' \<sharp>* B'\<close> \<open>x \<sharp> B'\<close> \<open>x \<sharp> B'\<close> \<open>yvec' \<sharp>* B\<close> \<open>y \<sharp> B\<close> \<open>set(map fst p) \<subseteq> supp B\<close>

      ultimately show ?case by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>B)"
      hence xSuppB: "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>B)"
        by(simp add: fresh_def)
      with EQ have ySuppB': "y \<in> supp (\<lparr>\<nu>*yvec'\<rparr>B')"
        by(rule boundOutputEqSupp)
      hence "y \<sharp> yvec'"
        by(induct yvec') (auto simp add: boundOutput.supp abs_supp)      
      with \<open>x \<sharp> yvec'\<close> EQ' have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')"
        by(simp add: eqvts)
      with  \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = length yvec'\<close> \<open>length xvec' = n\<close> IH
      obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "B = p \<bullet> [(x, y)] \<bullet> B'"
                 and "set(map fst p) \<subseteq> supp B" and "xvec' \<sharp>* ([(x, y)] \<bullet> B')" and "yvec' \<sharp>* B" 
        by blast

      from xSuppB have "x \<sharp> xvec'"
        by(induct xvec') (auto simp add: boundOutput.supp abs_supp)      
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
        apply(induct p)
        by(auto simp add: name_list_supp) (auto simp add: fresh_def) 
      from S have "(set ((x, y)#p)) \<subseteq> (set(x#xvec')) \<times> (set(y#yvec'))"
        by force
      moreover from \<open>x \<noteq> y\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> S \<open>distinctPerm p\<close>
      have "distinctPerm((x,y)#p)" by simp
      moreover from \<open>B = p \<bullet> [(x, y)] \<bullet> B'\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> have "B = [(x, y)] \<bullet> p \<bullet> B'"
        by(subst perm_compose) simp
      hence "B = ((x, y)#p) \<bullet> B'" by simp
      moreover from \<open>xvec' \<sharp>* ([(x, y)] \<bullet> B')\<close> have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> B')"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>x \<sharp> B'\<close> have "(x#xvec') \<sharp>* B'" by simp
      moreover from \<open>y \<sharp> B\<close> \<open>yvec' \<sharp>* B\<close> have "(y#yvec') \<sharp>* B" by simp
      moreover from \<open>set(map fst p) \<subseteq> supp B\<close> xSuppB \<open>x \<sharp> xvec'\<close>
      have "set(map fst ((x, y)#p)) \<subseteq> supp B"
        by(simp add: BOresChainSupp)
      ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
        by metis
    qed
  qed
qed

lemma boundOutputChainEqLength:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: "'a::fs_name"
  and   Q    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<close> have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec M P N Q)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
      by simp
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q::('a, 'b, 'c) psi); n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P  = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(simp add: alpha boundOutput.inject)
      with IH \<open>length xvec' = n\<close> have "length xvec' = length yvec'"
        by blast
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(simp add: alpha boundOutput.inject)
      hence "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
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

lemma boundOutputChainEq':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "xvec \<sharp>* yvec"

  shows "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  M = p \<bullet> N \<and>  P = p \<bullet> Q \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> yvec \<sharp>* M \<and> yvec \<sharp>* P"
using assms
apply(frule_tac boundOutputChainEqLength)
apply(drule_tac boundOutputChainEq)
by(auto simp add: boundOutput.inject)

lemma boundOutputChainEq'':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinctPerm p" and "yvec = p \<bullet> xvec" and "N = p \<bullet> M" and "Q = p \<bullet> P" and "xvec \<sharp>* N" and "xvec \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* P"
proof -

  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinctPerm p; yvec = p \<bullet> xvec; N = p \<bullet> M; Q = p \<bullet> P; xvec \<sharp>* N; xvec \<sharp>* Q; (p \<bullet> xvec) \<sharp>* M; (p \<bullet> xvec) \<sharp>* P\<rbrakk> \<Longrightarrow> thesis"

  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> (p \<bullet> xvec) \<sharp>* M \<and> (p \<bullet> xvec) \<sharp>* P"
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M P N Q)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by auto
    from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>(M::'a) \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q; xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P \<and> xvec \<sharp>* N \<and> xvec \<sharp>* Q \<and> (p \<bullet> xvec) \<sharp>* M \<and> (p \<bullet> xvec) \<sharp>* P"
      by fact 
    from EQ \<open>x \<noteq> y\<close>  \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>x \<sharp> xvec'\<close> have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)" and "x \<sharp> N" and "x \<sharp> Q" and "y \<sharp> M" and "y \<sharp> P"
      apply -
      apply(simp add: boundOutput.inject alpha eqvts)
      apply(simp add: boundOutput.inject alpha eqvts)
      apply(simp add: boundOutput.inject alpha eqvts)
      by(simp add: boundOutput.inject alpha' eqvts)+
    with \<open>xvec' \<sharp>* yvec'\<close> \<open>distinct xvec'\<close> \<open>distinct yvec'\<close> \<open>length xvec' = n\<close> IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "yvec' = p \<bullet> xvec'" and "([(x, y)] \<bullet> N) = p \<bullet> M" and "([(x, y)] \<bullet> Q) = p \<bullet> P" and "xvec' \<sharp>* ([(x, y)] \<bullet> N)" and "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" and "yvec' \<sharp>* M" and "yvec' \<sharp>* P"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from \<open>x \<sharp> xvec'\<close> \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S \<open>distinctPerm p\<close> \<open>x \<noteq> y\<close> have "distinctPerm((x, y)#p)" by auto
    moreover from \<open>yvec' = p \<bullet> xvec'\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: eqvts calc_atm perm_compose freshChainSimps)
    moreover from \<open>([(x, y)] \<bullet> N) = p \<bullet> M\<close>
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> M"
      by(simp add: pt_bij)
    hence "N = ((x, y)#p) \<bullet> M" by simp
    moreover from \<open>([(x, y)] \<bullet> Q) = p \<bullet> P\<close>
    have "([(x, y)] \<bullet> [(x, y)] \<bullet> Q) = [(x, y)] \<bullet> p \<bullet> P"
      by(simp add: pt_bij)
    hence "Q = ((x, y)#p) \<bullet> P" by simp
    moreover from \<open>xvec' \<sharp>* ([(x, y)] \<bullet> N)\<close> have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> N)"
      by(subst fresh_star_bij)
    with \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "xvec' \<sharp>* N" by simp
    with \<open>x \<sharp> N\<close> have "(x#xvec') \<sharp>* N" by simp
    moreover from \<open>xvec' \<sharp>* ([(x, y)] \<bullet> Q)\<close> have "([(x, y)] \<bullet> xvec') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> Q)"
      by(subst fresh_star_bij)
    with \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "xvec' \<sharp>* Q" by simp
    with \<open>x \<sharp> Q\<close> have "(x#xvec') \<sharp>* Q" by simp
    moreover from \<open>y \<sharp> M\<close> \<open>yvec' \<sharp>* M\<close> have "(y#yvec') \<sharp>* M" by simp
    moreover from \<open>y \<sharp> P\<close> \<open>yvec' \<sharp>* P\<close> have "(y#yvec') \<sharp>* P" by simp
    ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      by metis
  qed
  ultimately show ?thesis by blast
qed

lemma boundOutputEqSupp':
  fixes x    :: name
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   y    :: name
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec\<rparr>N \<prec>' Q)"
  and     "x \<noteq> y"
  and     "x \<sharp> yvec"
  and     "x \<sharp> xvec"
  and     "y \<sharp> xvec"
  and     "y \<sharp> yvec"
  and     "xvec \<sharp>* yvec"
  and     "x \<in> supp M"
  
  shows "y \<in> supp N"
proof -
  from Eq \<open>x \<noteq> y\<close> \<open>x \<sharp> yvec\<close> \<open>y \<sharp> yvec\<close> have "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(simp add: boundOutput.inject alpha eqvts)
  then obtain p where S: "set p \<subseteq> set xvec \<times> set yvec" and "M = p \<bullet> [(x, y)] \<bullet> N" and "distinctPerm p" using \<open>xvec \<sharp>* yvec\<close>
    by(blast dest: boundOutputChainEq')
  with \<open>x \<in> supp M\<close> have "x \<in> supp(p \<bullet> [(x, y)] \<bullet> N)" by simp
  hence "(p \<bullet> x) \<in> p \<bullet> supp(p \<bullet> [(x, y)] \<bullet> N)"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> S \<open>distinctPerm p\<close> have "x \<in> supp([(x, y)] \<bullet> N)"
    by(simp add: eqvts)
  hence "([(x, y)] \<bullet> x) \<in> ([(x, y)] \<bullet> (supp([(x, y)] \<bullet> N)))"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>x \<noteq> y\<close> show ?thesis by(simp add: calc_atm eqvts)
qed

lemma boundOutputChainOpenIH:
  fixes xvec :: "name list"
  and   x    :: name
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"
  and   yvec :: "name list"
  and   y    :: name
  and   B'   :: "('a, 'b, 'c) boundOutput"

  assumes Eq: "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>B) = \<lparr>\<nu>*yvec\<rparr>(\<lparr>\<nu>y\<rparr>B')"
  and     L: "length xvec = length yvec"
  and     xFreshB': "x \<sharp> B'"
  and     xFreshxvec: "x \<sharp> xvec"
  and     xFreshyvec: "x \<sharp> yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>([(x, y)] \<bullet> B')"
using assms
proof(induct n=="length xvec" arbitrary: xvec yvec y B' rule: nat.induct)
  case(zero xvec yvec y B')
  have "0 = length xvec" and "length xvec = length yvec" by fact+
  moreover have "\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec\<rparr>\<lparr>\<nu>y\<rparr>B'" by fact
  ultimately show ?case by(auto simp add: boundOutput.inject alpha)
next
  case(Suc n xvec yvec y B')
  have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
  then obtain x' xvec' y' yvec' where xEq: "xvec = x'#xvec'" and yEq: "yvec = y'#yvec'"
                                  and L': "length xvec' = length yvec'"
    by(cases xvec, auto, cases yvec, auto)
  have xFreshB': "x \<sharp> B'" by fact
  have "x \<sharp> xvec" and "x \<sharp> yvec" by fact+
  with xEq yEq have xineqx': "x \<noteq> x'" and xFreshxvec': "x \<sharp> xvec'"
                and xineqy': "x \<noteq> y'" and xFreshyvec': "x \<sharp> yvec'"
    by simp+
  have "\<lparr>\<nu>*xvec\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec\<rparr>\<lparr>\<nu>y\<rparr>B'" by fact
  with xEq yEq have Eq: "\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B')" by simp
  have "Suc n = length xvec" by fact
  with xEq have L'': "n = length xvec'" by simp
  have "\<lparr>\<nu>x'\<rparr>(\<lparr>\<nu>*xvec'\<rparr>B) = \<lparr>\<nu>y'\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B'))"
  proof(case_tac "x'=y'")
    assume x'eqy': "x' = y'"
    with Eq have "\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B'" by(simp add: boundOutput.inject alpha)
    hence "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')" using L' xFreshB' xFreshxvec' xFreshyvec' L'' 
      by(rule_tac Suc)
    with x'eqy' show ?thesis by(simp add: boundOutput.inject alpha)
  next
    assume x'ineqy': "x' \<noteq> y'"
    with Eq have Eq': "\<lparr>\<nu>*xvec'\<rparr>\<lparr>\<nu>x\<rparr>B = \<lparr>\<nu>*([(x', y')] \<bullet> yvec')\<rparr>\<lparr>\<nu>([(x', y')] \<bullet> y)\<rparr>([(x', y')] \<bullet> B')"
             and x'FreshB': "x' \<sharp> \<lparr>\<nu>*yvec'\<rparr>\<lparr>\<nu>y\<rparr>B'"
      by(simp add: boundOutput.inject alpha eqvts)+
    from L' have "length xvec' = length ([(x', y')] \<bullet> yvec')" by simp
    moreover from xineqx' xineqy' xFreshB' have "x \<sharp> [(x', y')] \<bullet> B'" by(simp add: fresh_left calc_atm)
    moreover from xineqx' xineqy' xFreshyvec' have "x \<sharp> [(x', y')] \<bullet> yvec'" by(simp add: fresh_left calc_atm)
    ultimately have "\<lparr>\<nu>*xvec'\<rparr>B = \<lparr>\<nu>*([(x', y')] \<bullet> yvec')\<rparr>([(x, ([(x', y')] \<bullet> y))] \<bullet> [(x', y')] \<bullet> B')" using Eq' xFreshxvec' L''
      by(rule_tac Suc)
    moreover from x'FreshB' have "x' \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> B')"
    proof(case_tac "x' \<sharp> yvec'")
      assume "x' \<sharp> yvec'"
      with x'FreshB' have x'FreshB': "x' \<sharp> \<lparr>\<nu>y\<rparr>B'"
        by(simp add: fresh_def BOresChainSupp)
      show ?thesis
      proof(case_tac "x'=y")
        assume x'eqy: "x' = y"
        show ?thesis
        proof(case_tac "x=y")
          assume "x=y"
          with xFreshB' x'eqy show ?thesis by(simp add: BOresChainSupp fresh_def)
        next
          assume "x \<noteq> y"
          with \<open>x \<sharp> B'\<close> have "y \<sharp> [(x, y)] \<bullet> B'" by(simp add: fresh_left calc_atm)
          with x'eqy show ?thesis by(simp add: BOresChainSupp fresh_def)
        qed
      next
        assume x'ineqy: "x' \<noteq> y"
        with x'FreshB' have "x' \<sharp> B'" by(simp add: abs_fresh)
        with xineqx' x'ineqy have "x' \<sharp> ([(x, y)] \<bullet> B')" by(simp add: fresh_left calc_atm)
        thus ?thesis by(simp add: BOresChainSupp fresh_def)
      qed
    next
      assume "\<not>x' \<sharp> yvec'"
      thus ?thesis by(simp add: BOresChainSupp fresh_def)
    qed
    ultimately show ?thesis using x'ineqy' xineqx' xineqy'
      apply(simp add: boundOutput.inject alpha eqvts)
      apply(subst perm_compose[of "[(x', y')]"])
      by(simp add: calc_atm)
  qed
  with xEq yEq show ?case by simp
qed

lemma boundOutputPar1Dest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* R"
  and     "yvec \<sharp>* R"

  obtains T where "P = T \<parallel> R" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>T. \<lbrakk>P = T \<parallel> R; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>T. P = T \<parallel> R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from \<open>xvec \<sharp>* R\<close> \<open>yvec \<sharp>* R\<close> \<open>xvec = x#xvec'\<close> \<open>yvec = y#yvec'\<close>
    have "x \<sharp> R" and "xvec' \<sharp>* R" and "y \<sharp> R" and "yvec' \<sharp>* R" by auto
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(simp add: boundOutput.inject alpha)
      with \<open>xvec' \<sharp>* R\<close> \<open>yvec' \<sharp>* R\<close> \<open>length xvec' = n\<close>
      obtain T where "P = T \<parallel> R" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(drule_tac Suc) auto
      with \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>x=y\<close> show ?case
        by(force simp add: boundOutput.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ \<open>x \<sharp> R\<close> \<open>y \<sharp> R\<close>
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> R)"
       and xFreshQR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(simp add: boundOutput.inject alpha eqvts)+
      moreover from \<open>yvec' \<sharp>* R\<close> have "([(x, y)] \<bullet> yvec') \<sharp>* ([(x, y)] \<bullet> R)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> R\<close> \<open>y \<sharp> R\<close> have "([(x, y)] \<bullet> yvec') \<sharp>* R" by simp
      moreover note \<open>xvec' \<sharp>* R\<close> \<open>length xvec' = n\<close>
      ultimately obtain T where "P = T \<parallel> R" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
        by(drule_tac Suc) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q))"
        by(simp add: boundOutput.inject alpha)
      moreover from xFreshQR have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(force simp add: boundOutputFresh)
      ultimately show ?thesis using \<open>P = T \<parallel> R\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> xFreshQR
        by(force simp add: alphaBoundOutput name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma boundOutputPar1Dest':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* yvec"

  obtains T p where "set p \<subseteq> set xvec \<times> set yvec" and "P = T \<parallel> (p \<bullet> R)" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>p T. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; P = T \<parallel> (p \<bullet> R); \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = T \<parallel> (p \<bullet> R) \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close> have "x \<noteq> y" and "x \<sharp> yvec'" and "y \<sharp> xvec'" and "xvec' \<sharp>* yvec'"
      by auto
    from Eq \<open>x \<noteq> y\<close> have Eq': "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
                     and xFreshQR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
      by(simp add: boundOutput.inject alpha)+
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R);  xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = T \<parallel> (p \<bullet> R) \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
      by fact
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P")
      assume "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P"
      with Eq have yFreshQR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(rule boundOutputEqFresh)
      with Eq' xFreshQR have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by simp
      with \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close>
      obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = T \<parallel> (p \<bullet> R)" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(drule_tac IH) auto
      from yFreshQR xFreshQR have yFreshQ: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" and xFreshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" 
        by(force simp add: BOresChainSupp fresh_def boundOutput.supp psi.supp)+
      hence "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by (subst alphaBoundOutput) simp+
      with A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by simp
      with \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> S \<open>P = T \<parallel> (p \<bullet> R)\<close> show ?case
        by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)"
      hence "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)" by(simp add: fresh_def)
      with Eq have "y \<in> supp(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
        by(rule boundOutputEqSupp)
      hence "y \<sharp> yvec'" by(simp add: BOresChainSupp fresh_def)
      with Eq' \<open>x \<sharp> yvec'\<close> have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> ([(x, y)] \<bullet> R))"
        by(simp add: eqvts)
      moreover note \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close>
      ultimately obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = T \<parallel> (p \<bullet> [(x, y)] \<bullet> R)" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
        by(drule_tac IH) auto

      from S have "set(p@[(x, y)]) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover from \<open>P = T \<parallel> (p \<bullet> [(x, y)] \<bullet> R)\<close>  have "P = T \<parallel> ((p @ [(x, y)]) \<bullet> R)"
        by(simp add: pt2[OF pt_name_inst])
      moreover from xFreshQR have xFreshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q" 
        by(force simp add: BOresChainSupp fresh_def boundOutput.supp psi.supp)+
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> \<open>x \<noteq> y\<close> have "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
        by(simp add: fresh_left calc_atm)
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)"
        by(subst alphaBoundOutput) (assumption | simp add: eqvts)+
      with  A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q)" by simp
      ultimately show ?thesis using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
        by(rule_tac x="p@[(x, y)]" in exI) force
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma boundOutputPar2Dest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* Q"
  and     "yvec \<sharp>* Q"

  obtains T where "P = Q \<parallel> T" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
proof -
  assume "\<And>T. \<lbrakk>P = Q \<parallel> T; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>T. P = Q \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from \<open>xvec \<sharp>* Q\<close> \<open>yvec \<sharp>* Q\<close> \<open>xvec = x#xvec'\<close> \<open>yvec = y#yvec'\<close>
    have "x \<sharp> Q" and "xvec' \<sharp>* Q" and "y \<sharp> Q" and "yvec' \<sharp>* Q" by auto
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R); xvec \<sharp>* Q; yvec \<sharp>* Q; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>T. P = Q \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(simp add: boundOutput.inject alpha)
      with \<open>xvec' \<sharp>* Q\<close> \<open>yvec' \<sharp>* Q\<close> \<open>length xvec' = n\<close>
      obtain T where "P = Q \<parallel> T" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
        by(drule_tac IH) auto
      with \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>x=y\<close> show ?case
        by(force simp add: boundOutput.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close>
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' (Q \<parallel> ([(x, y)] \<bullet> R))"
       and xFreshQR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(simp add: boundOutput.inject alpha eqvts)+
      moreover from \<open>yvec' \<sharp>* Q\<close> have "([(x, y)] \<bullet> yvec') \<sharp>* ([(x, y)] \<bullet> Q)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> have "([(x, y)] \<bullet> yvec') \<sharp>* Q" by simp
      moreover note \<open>xvec' \<sharp>* Q\<close> \<open>length xvec' = n\<close>
      ultimately obtain T where "P = Q \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
        by(drule_tac IH) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R))"
        by(simp add: boundOutput.inject alpha)
      moreover from xFreshQR have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
        by(force simp add: boundOutputFresh)
      ultimately show ?thesis using \<open>P = Q \<parallel> T\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> xFreshQR
        by(force simp add: alphaBoundOutput name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma boundOutputPar2Dest':
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)"
  and     "xvec \<sharp>* yvec"

  obtains T p where "set p \<subseteq> set xvec \<times> set yvec" and "P = (p \<bullet> Q) \<parallel> T" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
proof -
  assume "\<And>p T. \<lbrakk>set p \<subseteq> set xvec \<times> set yvec; P = (p \<bullet> Q) \<parallel> T; \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = (p \<bullet> Q) \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
  proof(induct n arbitrary: xvec yvec M N P Q R)
    case(0 xvec yvec M N P Q R)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M N P Q R)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R)\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' (Q \<parallel> R)"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence Eq: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close> have "x \<noteq> y" and "x \<sharp> yvec'" and "y \<sharp> xvec'" and "xvec' \<sharp>* yvec'"
      by auto
    from Eq \<open>x \<noteq> y\<close> have Eq': "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = [(x, y)] \<bullet> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
                     and xFreshQR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
      by(simp add: boundOutput.inject alpha)+
    have IH: "\<And>xvec yvec M N P Q R. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (Q \<parallel> R);  xvec \<sharp>* yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p T. set p \<subseteq> set xvec \<times> set yvec \<and> P = (p \<bullet> Q) \<parallel> T \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R"
      by fact
    show ?case
    proof(case_tac "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P")
      assume "x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P"
      with Eq have yFreshQR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by(rule boundOutputEqFresh)
      with Eq' xFreshQR have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R)"
        by simp
      with \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close>
      obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = (p \<bullet> Q) \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R"
        by(drule_tac IH) auto
      from yFreshQR xFreshQR have yFreshR: "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" and xFreshQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" 
        by(force simp add: BOresChainSupp fresh_def boundOutput.supp psi.supp)+
      hence "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by (subst alphaBoundOutput) simp+
      with A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by simp
      with \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> S \<open>P = (p \<bullet> Q) \<parallel> T\<close> show ?case
        by auto
    next
      assume "\<not>(x \<sharp> \<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)"
      hence "x \<in> supp(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P)" by(simp add: fresh_def)
      with Eq have "y \<in> supp(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' (Q \<parallel> R))"
        by(rule boundOutputEqSupp)
      hence "y \<sharp> yvec'" by(simp add: BOresChainSupp fresh_def)
      with Eq' \<open>x \<sharp> yvec'\<close> have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' (([(x, y)] \<bullet> Q) \<parallel> ([(x, y)] \<bullet> R))"
        by(simp add: eqvts)
      moreover note \<open>xvec' \<sharp>* yvec'\<close> \<open>length xvec' = n\<close>
      ultimately obtain p T where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "P = (p \<bullet> [(x, y)] \<bullet> Q) \<parallel> T" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T = \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
        by(drule_tac IH) auto

      from S have "set(p@[(x, y)]) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
      moreover from \<open>P = (p \<bullet> [(x, y)] \<bullet> Q) \<parallel> T\<close>  have "P = ((p @ [(x, y)]) \<bullet> Q) \<parallel> T"
        by(simp add: pt2[OF pt_name_inst])
      moreover from xFreshQR have xFreshR: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' R" 
        by(force simp add: BOresChainSupp fresh_def boundOutput.supp psi.supp)+
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> \<open>x \<noteq> y\<close> have "y \<sharp> \<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)"
        by(simp add: fresh_left calc_atm)
      with \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec'\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> R)) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)"
        by(subst alphaBoundOutput) (assumption | simp add: eqvts)+
      with  A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' T) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' R)" by simp
      ultimately show ?thesis using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
        by(rule_tac x="p@[(x, y)]" in exI) force
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma boundOutputApp:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   B    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) boundOutput"

  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>B = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>B)"
by(induct xvec) auto
  
lemma openInjectAuxAuxAux:
  fixes x    :: name
  and   xvec :: "name list"

  shows "\<exists>y yvec. x # xvec = yvec @ [y] \<and> length xvec = length yvec"
apply(induct xvec arbitrary: x)
apply auto
apply(subgoal_tac "\<exists>y yvec. a # xvec = yvec @ [y] \<and> length xvec = length yvec")
apply(clarify)
apply(rule_tac x=y in exI)
by auto

lemma openInjectAuxAux:
  fixes xvec1 :: "name list"
  and   xvec2 :: "name list"
  and   yvec  :: "name list"

  assumes "length(xvec1@xvec2) = length yvec"

  shows "\<exists>yvec1 yvec2. yvec = yvec1@yvec2 \<and> length xvec1 = length yvec1 \<and> length xvec2 = length yvec2"
using assms
apply(induct yvec arbitrary: xvec1)
apply simp
apply simp
apply(case_tac xvec1)
apply simp
apply simp
apply(subgoal_tac "\<exists>yvec1 yvec2.
                   yvec = yvec1 @ yvec2 \<and> length list = length yvec1 \<and> length xvec2 = length yvec2")
apply(clarify)
apply(rule_tac x="a#yvec1" in exI)
apply(rule_tac x=yvec2 in exI)
by auto

lemma openInjectAux:
  fixes xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   yvec  :: "name list"

  assumes "length(xvec1@x#xvec2) = length yvec"

  shows "\<exists>yvec1 y yvec2. yvec = yvec1@y#yvec2 \<and> length xvec1 = length yvec1 \<and> length xvec2 = length yvec2"
using assms
apply(case_tac yvec)
apply simp
apply simp
apply(subgoal_tac "\<exists>(yvec1::name list) (yvec2::name list). yvec1@yvec2 = list \<and> length xvec1 = length yvec1 \<and> length xvec2 = length yvec2")
apply(clarify)
apply hypsubst_thin
apply simp
apply(subgoal_tac "\<exists>y (yvec::name list). a # yvec1 = yvec @ [y] \<and> length yvec1 = length yvec")
apply(clarify)
apply(rule_tac x=yvec in exI)
apply(rule_tac x=y in exI)
apply simp
apply(rule_tac x=yvec2 in exI)
apply simp
apply(rule openInjectAuxAuxAux)
apply(insert openInjectAuxAux)
apply simp
by blast

lemma boundOutputOpenDest:
  fixes yvec  :: "name list"
  and   M     :: "'a::fs_name"
  and   P     :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   N     :: 'a
  and   Q     :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "x \<sharp> xvec1"
  and     "x \<sharp> yvec"
  and     "x \<sharp> N"
  and     "x \<sharp> Q"
  and     "distinct yvec"
  

  obtains yvec1 y yvec2 where "yvec=yvec1@y#yvec2" and "length xvec1 = length yvec1" and "length xvec2 = length yvec2" 
                          and "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
proof -
  assume Ass: "\<And>yvec1 y yvec2.
        \<lbrakk>yvec = yvec1 @ y # yvec2; length xvec1 = length yvec1; length xvec2 = length yvec2;
         \<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1 @ yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)\<rbrakk>
        \<Longrightarrow> thesis"
  from Eq have "length(xvec1@x#xvec2) = length yvec" by(rule boundOutputChainEqLength)
  then obtain yvec1 y yvec2 where A: "yvec = yvec1@y#yvec2" and "length xvec1 = length yvec1"
          and "length xvec2 = length yvec2"
    by(metis openInjectAux sym)

  from \<open>distinct yvec\<close> A have "y \<sharp> yvec2" by simp
  from A \<open>x \<sharp> yvec\<close> have "x \<sharp> yvec2" and "x \<sharp> yvec1"  by simp+
  with Eq \<open>length xvec1 = length yvec1\<close> \<open>x \<sharp> N\<close> \<open>x \<sharp> Q\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> xvec1\<close> A
  have "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(force dest: boundOutputChainOpenIH simp add: boundOutputApp BOresChainSupp fresh_def boundOutput.supp eqvts)
  with \<open>length xvec1 = length yvec1\<close> \<open>length xvec2 = length yvec2\<close> A Ass show ?thesis
    by blast
qed

lemma boundOutputOpenDest':
  fixes yvec  :: "name list"
  and   M     :: "'a::fs_name"
  and   P     :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   xvec1 :: "name list"
  and   x     :: name
  and   xvec2 :: "name list"
  and   N     :: 'a
  and   Q     :: "('a, 'b, 'c) psi"

  assumes Eq: "\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  and     "x \<sharp> xvec1"
  and     "x \<sharp> yvec"
  and     "x \<sharp> N"
  and     "x \<sharp> Q"
  

  obtains yvec1 y yvec2 where "yvec=yvec1@y#yvec2" and "length xvec1 = length yvec1" and "length xvec2 = length yvec2" 
                          and "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@[(x, y)] \<bullet> yvec2)\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
proof -
  assume Ass: "\<And>yvec1 y yvec2.
        \<lbrakk>yvec = yvec1 @ y # yvec2; length xvec1 = length yvec1; length xvec2 = length yvec2;
         \<lparr>\<nu>*(xvec1 @ xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1 @ ([(x, y)] \<bullet> yvec2))\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)\<rbrakk>
        \<Longrightarrow> thesis"
  from Eq have "length(xvec1@x#xvec2) = length yvec" by(rule boundOutputChainEqLength)
  then obtain yvec1 y yvec2 where A: "yvec = yvec1@y#yvec2" and "length xvec1 = length yvec1"
          and "length xvec2 = length yvec2"
    by(metis openInjectAux sym)

  from A \<open>x \<sharp> yvec\<close> have "x \<sharp> yvec2" and "x \<sharp> yvec1"  by simp+
  with Eq \<open>length xvec1 = length yvec1\<close> \<open>x \<sharp> N\<close> \<open>x \<sharp> Q\<close> \<open>x \<sharp> xvec1\<close> A
  have "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>M \<prec>' P = \<lparr>\<nu>*(yvec1@([(x, y)] \<bullet> yvec2))\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
    by(force dest: boundOutputChainOpenIH simp add: boundOutputApp BOresChainSupp fresh_def boundOutput.supp eqvts)
  with \<open>length xvec1 = length yvec1\<close> \<open>length xvec2 = length yvec2\<close> A Ass show ?thesis
    by blast
qed

lemma boundOutputScopeDest:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   x    :: name
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
  and     "z \<sharp> xvec"
  and     "z \<sharp> yvec"

  obtains R where "P = \<lparr>\<nu>z\<rparr>R" and "\<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
proof -
  assume "\<And>R. \<lbrakk>P = \<lparr>\<nu>z\<rparr>R; \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>R. P = \<lparr>\<nu>z\<rparr>R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
  proof(induct n arbitrary: xvec yvec M N P Q z)
    case(0 xvec yvec M N P Q z)
    have Eq: "\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: boundOutput.inject)
  next
    case(Suc n xvec yvec M N P Q z)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>\<lparr>\<nu>*xvec\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec\<rparr>N \<prec>' (\<lparr>\<nu>z\<rparr>Q)\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "\<lparr>\<nu>*(x#xvec')\<rparr>M \<prec>' P = \<lparr>\<nu>*(y#yvec')\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P) = \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q)"
      by simp
    from \<open>z \<sharp> xvec\<close> \<open>z \<sharp> yvec\<close> \<open>xvec = x#xvec'\<close> \<open>yvec = y#yvec'\<close>
    have "z \<noteq> x" and "z \<noteq> y" and "z \<sharp> xvec'" and "z \<sharp> yvec'"
      by simp+
    have IH: "\<And>xvec yvec M N P Q z. \<lbrakk>\<lparr>\<nu>*xvec\<rparr>M \<prec>' (P::('a, 'b, 'c) psi) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q; z \<sharp> xvec; z \<sharp> yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>R. P = \<lparr>\<nu>z\<rparr>R \<and> \<lparr>\<nu>*xvec\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec\<rparr>N \<prec>' Q"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
        by(simp add: boundOutput.inject alpha)
      with \<open>z \<sharp> xvec'\<close> \<open>z \<sharp> yvec'\<close> \<open>length xvec' = n\<close>
      obtain R where "P = \<lparr>\<nu>z\<rparr>R" and "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R = \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(drule_tac IH) auto
      with \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>x=y\<close> show ?case
        by(force simp add: boundOutput.inject alpha)
    next
      assume "x \<noteq> y"
      with EQ \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close>
      have "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' \<lparr>\<nu>z\<rparr>([(x, y)] \<bullet> Q)"
       and xFreshzQ: "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' \<lparr>\<nu>z\<rparr>Q"
        by(simp add: boundOutput.inject alpha eqvts)+
      moreover from \<open>z \<noteq> x\<close> \<open>z \<noteq> y\<close> \<open>z \<sharp> yvec'\<close> \<open>x \<noteq> y\<close> have "z \<sharp> ([(x, y)] \<bullet> yvec')"
        by(simp add: fresh_left calc_atm)
      moreover note \<open>z \<sharp> xvec'\<close> \<open>length xvec' = n\<close>
      ultimately obtain R where "P = \<lparr>\<nu>z\<rparr>R" and A: "\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q)"
        by(drule_tac IH) auto

      from A have "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec'\<rparr>M \<prec>' R) = \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> N) \<prec>' ([(x, y)] \<bullet> Q))"
        by(simp add: boundOutput.inject alpha)
      moreover from xFreshzQ \<open>z \<noteq> x\<close> have "x \<sharp> \<lparr>\<nu>*yvec'\<rparr>N \<prec>' Q"
        by(simp add: boundOutputFresh abs_fresh)
      ultimately show ?thesis using \<open>P = \<lparr>\<nu>z\<rparr>R\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> xFreshzQ
        by(force simp add: alphaBoundOutput name_swap eqvts)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

nominal_datatype ('a, 'b, 'c) residual = 
  RIn "'a::fs_name" 'a "('a, 'b::fs_name, 'c::fs_name) psi" 
| ROut 'a "('a, 'b, 'c) boundOutput"
| RTau "('a, 'b, 'c) psi"

nominal_datatype 'a action = In "'a::fs_name" 'a      ("_\<lparr>_\<rparr>" [90, 90] 90)
                   | Out "'a::fs_name" "name list" 'a ("_\<lparr>\<nu>*_\<rparr>\<langle>_\<rangle>" [90, 90, 90] 90)
                   | Tau                              ("\<tau>" 90)

nominal_primrec bn :: "('a::fs_name) action \<Rightarrow> name list"
  where
  "bn (M\<lparr>N\<rparr>) = []"
| "bn (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = xvec"
| "bn (\<tau>) = []"
by(rule TrueI)+

lemma bnEqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> bn \<alpha>) = bn(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

nominal_primrec create_residual :: "('a::fs_name) action \<Rightarrow> ('a, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) residual" ("_ \<prec> _" [80, 80] 80)
where 
  "(M\<lparr>N\<rparr>) \<prec> P = RIn M N P"
| "M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P = ROut M (\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
| "\<tau> \<prec> P = (RTau P)"
by(rule TrueI)+

nominal_primrec subject :: "('a::fs_name) action \<Rightarrow> 'a option" 
  where 
  "subject (M\<lparr>N\<rparr>) = Some M"
| "subject (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some M"
| "subject (\<tau>) = None"
by(rule TrueI)+

nominal_primrec object :: "('a::fs_name) action \<Rightarrow> 'a option" 
  where 
  "object (M\<lparr>N\<rparr>) = Some N"
| "object (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) = Some N"
| "object (\<tau>) = None"
by(rule TrueI)+

lemma optionFreshChain[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"

  shows "xvec \<sharp>* (Some x) = xvec \<sharp>* x"
  and   "X \<sharp>* (Some x) = X \<sharp>* x"
  and   "xvec \<sharp>* None"
  and   "X \<sharp>* None"
by(auto simp add: fresh_star_def fresh_some fresh_none)

lemmas [simp] = fresh_some fresh_none
  
lemma actionFresh[simp]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"

  shows "(x \<sharp> \<alpha>)  = (x \<sharp> (subject \<alpha>) \<and> x \<sharp> (bn \<alpha>) \<and> x \<sharp> (object \<alpha>))"
by(nominal_induct \<alpha> rule: action.strong_induct) auto
  
lemma actionFreshChain[simp]:
  fixes X    :: "name set"
  and   \<alpha>    :: "('a::fs_name) action"
  and   xvec :: "name list"

  shows "(X \<sharp>* \<alpha>) = (X \<sharp>* (subject \<alpha>) \<and> X \<sharp>* (bn \<alpha>) \<and> X \<sharp>* (object \<alpha>))"
  and   "(xvec \<sharp>* \<alpha>) = (xvec \<sharp>* (subject \<alpha>) \<and> xvec \<sharp>* (bn \<alpha>) \<and> xvec \<sharp>* (object \<alpha>))"
by(auto simp add: fresh_star_def)

lemma subjectEqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> subject \<alpha>) = subject(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma okjectEqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"

  shows "(p \<bullet> object \<alpha>) = object(p \<bullet> \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma create_residualEqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(p \<bullet> (\<alpha> \<prec> P)) = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P)"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: eqvts)

lemma residualFresh:
  fixes x :: name
  and   \<alpha> :: "'a::fs_name action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "(x \<sharp> (\<alpha> \<prec> P)) = (x \<sharp> (subject \<alpha>) \<and> (x \<in> (set(bn(\<alpha>))) \<or> (x \<sharp> object(\<alpha>) \<and> x \<sharp> P)))"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: fresh_some fresh_none boundOutputFresh)

lemma residualFresh2[simp]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "x \<sharp> \<alpha>"
  and     "x \<sharp> P"

  shows "x \<sharp> \<alpha> \<prec> P"
using assms
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma residualFreshChain2[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "\<lbrakk>xvec \<sharp>* \<alpha>; xvec \<sharp>* P\<rbrakk> \<Longrightarrow> xvec \<sharp>* (\<alpha> \<prec> P)"
  and   "\<lbrakk>X \<sharp>* \<alpha>; X \<sharp>* P\<rbrakk> \<Longrightarrow> X \<sharp>* (\<alpha> \<prec> P)"
by(auto simp add: fresh_star_def)

lemma residualFreshSimp[simp]:
  fixes x :: name
  and   M :: "'a::fs_name"
  and   N :: 'a
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  

  shows "x \<sharp> (M\<lparr>N\<rparr> \<prec> P) = (x \<sharp> M \<and> x \<sharp> N \<and> x \<sharp> P)"
  and   "x \<sharp> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P) = (x \<sharp> M \<and> x \<sharp> (\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P)))"
  and   "x \<sharp> (\<tau> \<prec> P) = (x \<sharp> P)"
by(auto simp add: residualFresh)

lemma residualInject':

  shows "(\<alpha> \<prec> P = RIn M N Q) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
  and   "(\<alpha> \<prec> P = ROut M B) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
  and   "(\<alpha> \<prec> P = RTau Q) = (\<alpha> = \<tau> \<and> P = Q)"
  and   "(RIn M N Q = \<alpha> \<prec> P) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
  and   "(ROut M B = \<alpha> \<prec> P) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
  and   "(RTau Q = \<alpha> \<prec> P) = (\<alpha> = \<tau> \<and> P = Q)"
proof -
  show "(\<alpha> \<prec> P = RIn M N Q) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(\<alpha> \<prec> P = ROut M B) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show  "(\<alpha> \<prec> P = RTau Q) = (\<alpha> = \<tau> \<and> P = Q)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(RIn M N Q = \<alpha> \<prec> P) = (P = Q \<and> \<alpha> = M\<lparr>N\<rparr>)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show "(ROut M B = \<alpha> \<prec> P) = (\<exists>xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<and> B = \<lparr>\<nu>*xvec\<rparr>(N \<prec>' P))"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
next
  show  "(RTau Q = \<alpha> \<prec> P) = (\<alpha> = \<tau> \<and> P = Q)"
    by(nominal_induct \<alpha> rule: action.strong_induct)
      (auto simp add: residual.inject action.inject)
qed

lemma residualFreshChainSimp[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   M    :: "'a::fs_name"
  and   N    :: 'a
  and   yvec :: "name list"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (M\<lparr>N\<rparr> \<prec> P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P) = (xvec \<sharp>* M \<and> xvec \<sharp>* (\<lparr>\<nu>*yvec\<rparr>(N \<prec>' P)))"
  and   "xvec \<sharp>* (\<tau> \<prec> P) = (xvec \<sharp>* P)"
  and   "X \<sharp>* (M\<lparr>N\<rparr> \<prec> P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* (M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P) = (X \<sharp>* M \<and> X \<sharp>* (\<lparr>\<nu>*yvec\<rparr>(N \<prec>' P)))"
  and   "X \<sharp>* (\<tau> \<prec> P) = (X \<sharp>* P)"
by(auto simp add: fresh_star_def)

lemma residualFreshChainSimp2[simp]:
  fixes xvec :: "name list"
  and   X    :: "name set"
  and   M    :: "'a::fs_name"
  and   N    :: 'a
  and   yvec :: "name list"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (RIn M N P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* (ROut M B) = (xvec \<sharp>* M \<and> xvec \<sharp>* B)"
  and   "xvec \<sharp>* (RTau P) = (xvec \<sharp>* P)"
  and   "X \<sharp>* (RIn M N P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* (ROut M B) = (X \<sharp>* M \<and> X \<sharp>* B)"
  and   "X \<sharp>* (RTau P) = (X \<sharp>* P)"
by(auto simp add: fresh_star_def)

lemma freshResidual3[dest]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "x \<sharp> bn \<alpha>"
  and     "x \<sharp> \<alpha> \<prec> P"

  shows "x \<sharp> \<alpha>" and "x \<sharp> P"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma freshResidualChain3[dest]:
  fixes xvec :: "name list"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "xvec \<sharp>* (\<alpha> \<prec> P)"
  and     "xvec \<sharp>* bn \<alpha>"

  shows "xvec \<sharp>* \<alpha>" and "xvec \<sharp>* P"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma freshResidual4[dest]:
  fixes x :: name
  and   \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "x \<sharp> \<alpha> \<prec> P"

  shows "x \<sharp> subject \<alpha>"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma freshResidualChain4[dest]:
  fixes xvec :: "name list"
  and   \<alpha>    :: "('a::fs_name) action"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  assumes "xvec \<sharp>* (\<alpha> \<prec> P)"

  shows "xvec \<sharp>* subject \<alpha>"
using assms
by(nominal_induct rule: action.strong_induct) auto

lemma alphaOutputResidual:
  fixes M    :: "'a::fs_name"
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   p    :: "name prm"

  assumes "(p \<bullet> xvec) \<sharp>* N"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and     "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "set xvec \<subseteq> set yvec"

  shows "M\<lparr>\<nu>*yvec\<rparr>\<langle>N\<rangle> \<prec> P = M\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P)"
using assms
by(simp add: boundOutputChainAlpha'')

lemmas[simp del] =  create_residual.simps

lemma residualInject'':

  assumes "bn \<alpha> = bn \<beta>"

  shows "(\<alpha> \<prec> P = \<beta> \<prec> Q) = (\<alpha> = \<beta> \<and> P = Q)"
using assms
apply(nominal_induct \<alpha> rule: action.strong_induct)
apply(auto simp add: residual.inject create_residual.simps residualInject' action.inject boundOutput.inject)
by(rule_tac x="bn \<beta>" in exI) auto

lemmas residualInject = residual.inject create_residual.simps residualInject' residualInject''

lemma bnFreshResidual[simp]:
  fixes \<alpha> :: "('a::fs_name) action"

  shows "(bn \<alpha>) \<sharp>* (\<alpha> \<prec> P) = bn \<alpha> \<sharp>* (subject \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct)
  (auto simp add: residualFresh fresh_some fresh_star_def)

lemma actionCases[case_names cInput cOutput cTau]:
  fixes \<alpha> :: "('a::fs_name) action"

  assumes "\<And>M N. \<alpha> = M\<lparr>N\<rparr> \<Longrightarrow> Prop"
  and     "\<And>M xvec N. \<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<Longrightarrow> Prop"
  and     "\<alpha> = \<tau> \<Longrightarrow> Prop"

  shows Prop
using assms
by(nominal_induct \<alpha> rule: action.strong_induct) auto

lemma actionPar1Dest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"

  obtains T p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn \<beta>)" and "P = T \<parallel> (p \<bullet> R)" and "\<alpha> \<prec> T = \<beta> \<prec> Q"
using assms
apply(cases rule: actionCases[where \<alpha>=\<alpha>])
apply(auto simp add: residualInject)
by(drule_tac boundOutputPar1Dest') auto

lemma actionPar2Dest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"

  obtains T p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn \<beta>)" and "P = (p \<bullet> Q) \<parallel> T" and "\<alpha> \<prec> T = \<beta> \<prec> R"
using assms
apply(cases rule: actionCases[where \<alpha>=\<alpha>])
apply(auto simp add: residualInject)
by(drule_tac boundOutputPar2Dest') auto

lemma actionScopeDest:
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  fixes \<beta> :: "('a::fs_name) action"
  and   x :: name
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> \<lparr>\<nu>x\<rparr>Q"
  and     "x \<sharp> bn \<alpha>"
  and     "x \<sharp> bn \<beta>"

  obtains R where "P = \<lparr>\<nu>x\<rparr>R" and "\<alpha> \<prec> R = \<beta> \<prec> Q"
using assms
apply(cases rule: actionCases[where \<alpha>=\<alpha>])
apply(auto simp add: residualInject)
by(drule_tac boundOutputScopeDest) auto

abbreviation
  outputJudge ("_\<langle>_\<rangle>" [110, 110] 110) where "M\<langle>N\<rangle> \<equiv> M\<lparr>\<nu>*([])\<rparr>\<langle>N\<rangle>"

declare [[unify_trace_bound=100]]

locale env = substPsi substTerm substAssert substCond + 
             assertion SCompose' SImp' SBottom' SChanEq'
  for substTerm :: "('a::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'a"
  and substAssert :: "('b::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'b"
  and substCond :: "('c::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'c"
  and SCompose'  :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and SImp'      :: "'b \<Rightarrow> 'c \<Rightarrow> bool"
  and SBottom'   :: 'b
  and SChanEq'   :: "'a \<Rightarrow> 'a \<Rightarrow> 'c"
begin
notation SCompose' (infixr "\<otimes>" 90)
notation SImp' ("_ \<turnstile> _" [85, 85] 85)
notation FrameImp ("_ \<turnstile>\<^sub>F _" [85, 85] 85) 
abbreviation
  FBottomJudge ("\<bottom>\<^sub>F" 90) where "\<bottom>\<^sub>F \<equiv> (FAssert SBottom')"
notation SChanEq' ("_ \<leftrightarrow> _" [90, 90] 90)
notation substTerm ("_[_::=_]" [100, 100, 100] 100)
notation subs ("_[_::=_]" [100, 100, 100] 100)
notation AssertionStatEq ("_ \<simeq> _" [80, 80] 80)
notation FrameStatEq ("_ \<simeq>\<^sub>F _" [80, 80] 80)
notation SBottom' ("\<one>" 190)
abbreviation insertAssertion' ("insertAssertion") where "insertAssertion' \<equiv> assertionAux.insertAssertion (\<otimes>)"

inductive semantics :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) residual \<Rightarrow> bool"
                       ("_ \<rhd> _ \<longmapsto> _" [50, 50, 50] 50)
where
  cInput:  "\<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N; xvec \<sharp>* Tvec;
            length xvec = length Tvec;
            xvec \<sharp>* \<Psi>; xvec \<sharp>* M; xvec \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto> K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
| Output: "\<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto> K\<langle>N\<rangle> \<prec> P"
| Case:   "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> Rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> Cases Cs \<longmapsto> Rs"

| cPar1:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>\<alpha> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>)\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)"
| cPar2:   "\<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; distinct(bn \<alpha>); 
             bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* (subject \<alpha>)\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
| cComm1:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; 
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| cComm2:   "\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto> M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
             \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; 
             A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
             A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; 
             A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P';
             A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec; distinct xvec;
             xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M;
             xvec \<sharp>* Q; xvec \<sharp>* K\<rbrakk> \<Longrightarrow>
             \<Psi> \<rhd> P \<parallel> Q \<longmapsto> \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
| cOpen:    "\<lbrakk>\<Psi> \<rhd> P \<longmapsto> M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; x \<sharp> xvec; x \<sharp> yvec; x \<sharp> M; x \<sharp> \<Psi>;
              distinct xvec; distinct yvec;
              xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M\<rbrakk> \<Longrightarrow>
              \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto> M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
| cScope:  "\<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')"
| Bang:    "\<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs; guarded P\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> !P \<longmapsto> Rs"

abbreviation
  semanticsBottomJudge ("_ \<longmapsto> _" [50, 50] 50) where "P \<longmapsto> Rs \<equiv> \<one> \<rhd> P \<longmapsto> Rs"

equivariance env.semantics

nominal_inductive2 env.semantics
  avoids cInput: "set xvec"
       | cPar1: "set A\<^sub>Q \<union> set(bn \<alpha>)"
       | cPar2: "set A\<^sub>P \<union> set(bn \<alpha>)"
       | cComm1: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec"
       | cComm2: "set A\<^sub>P \<union> set A\<^sub>Q \<union> set xvec"
       | cOpen:  "{x} \<union> set xvec \<union> set yvec"
       | cScope: "{x} \<union> set(bn \<alpha>)"
apply(auto intro: substTerm.subst4Chain subst4Chain simp add: abs_fresh residualFresh)
apply(force simp add: fresh_star_def abs_fresh)
apply(simp add: boundOutputFresh)
apply(simp add: boundOutputFreshSet)
apply(simp add: boundOutputFreshSet)
by(simp add: fresh_star_def abs_fresh)

lemma nilTrans[dest]:
  fixes \<Psi>   :: 'b
  and   Rs   :: "('a, 'b, 'c) residual"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   yvec :: "name list"
  and   N'   :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   CsP  :: "('c \<times>  ('a, 'b, 'c) psi) list"
  and   \<Psi>'   :: 'b

  shows "\<Psi> \<rhd> \<zero> \<longmapsto> Rs \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>\<nu>*yvec\<rparr>\<langle>N'\<rangle> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<lparr>N'\<rparr> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> False"
  and   "\<Psi> \<rhd> \<lbrace>\<Psi>'\<rbrace> \<longmapsto> Rs \<Longrightarrow> False"
apply(cases rule: semantics.cases) apply auto
apply(cases rule: semantics.cases) apply(auto simp add: residualInject)
apply(cases rule: semantics.cases) apply(auto simp add: residualInject)
apply(cases rule: semantics.cases) apply(auto simp add: residualInject)
apply(cases rule: semantics.cases) apply(auto simp add: residualInject)
by(cases rule: semantics.cases) (auto simp add: residualInject)
  
lemma residualEq:
  fixes \<alpha> :: "'a action"
  and   P :: "('a, 'b, 'c) psi"
  and   \<beta> :: "'a action"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> Q"
  and     "bn \<alpha> \<sharp>* (bn \<beta>)"
  and     "distinct(bn \<alpha>)"
  and     "distinct(bn \<beta>)"
  and     "bn \<alpha> \<sharp>* (\<alpha> \<prec> P)"
  and     "bn \<beta> \<sharp>* (\<beta> \<prec> Q)"

  obtains p where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "\<beta> = p \<bullet> \<alpha>" and "Q = p \<bullet> P" and "bn \<alpha> \<sharp>* \<beta>" and "bn \<alpha> \<sharp>* Q" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* P"
using assms
proof(nominal_induct \<alpha> rule: action.strong_induct)
  case(In M N)
  thus ?case by(simp add: residualInject)
next
  case(Out M xvec N)
  thus ?case 
    by(auto simp add: residualInject)
      (drule_tac boundOutputChainEq'', auto) 
next
  case Tau
  thus ?case by(simp add: residualInject)
qed

lemma semanticsInduct[consumes 3, case_names cAlpha cInput cOutput cCase cPar1 cPar2 cComm1 cComm2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* (subject \<alpha>)"
  and     "distinct(bn \<alpha>)"
  and     rAlpha: "\<And>\<Psi> P \<alpha> P' p C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); 
                                    bn \<alpha> \<sharp>* C; bn \<alpha> \<sharp>* (bn(p \<bullet> \<alpha>)); 
                                    set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinctPerm p;
                                    (bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; Prop C \<Psi> P \<alpha> P'\<rbrakk> \<Longrightarrow>
                                     Prop C \<Psi> P (p \<bullet> \<alpha>) (p \<bullet> P')"
  and     rInput: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              (K\<lparr>(N[xvec::=Tvec])\<rparr>) (P[xvec::=Tvec])"
  and     rOutput: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (K\<langle>N\<rangle>) P"
  and     rCase: "\<And>\<Psi> P \<alpha> P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<alpha> P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                      Prop C \<Psi> (Cases Cs) \<alpha> P'"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; distinct(bn \<alpha>); bn \<alpha> \<sharp>* Q;
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q')"
  and     rComm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>N\<rparr>) P'; 
                    extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q'; 
                    extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rComm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P'; 
                    extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>N\<rparr>) Q'; 
                    extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q'; distinct xvec;
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rOpen:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;  distinct xvec; distinct yvec;
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     rScope: "\<And>\<Psi> P \<alpha> P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; \<And>C. Prop C \<Psi> P \<alpha> P';
                    x \<sharp> \<Psi>; x \<sharp> \<alpha>; bn \<alpha> \<sharp>* \<Psi>;
                    bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* (subject \<alpha>); x \<sharp> C; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
  and     rBang:    "\<And>\<Psi> P \<alpha> P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<alpha> P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) \<alpha> P'"

  shows "Prop C \<Psi> P \<alpha> P'"
using \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* (subject \<alpha>)\<close> \<open>distinct(bn \<alpha>)\<close>
proof(nominal_induct x3=="\<alpha> \<prec> P'" avoiding: \<alpha> C arbitrary: P' rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P \<alpha> C P')
  thus ?case by(force intro: rInput simp add: residualInject)
next
  case(Output \<Psi> M K N P \<alpha> C P')
  thus ?case by(force intro: rOutput simp add: residualInject)
next
  case(Case \<Psi> P Rs \<phi> Cs \<alpha> C)
  thus ?case by(auto intro: rCase)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q \<alpha>' C P'')
  note \<open>\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> P''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> Q)" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (P' \<parallel> Q)" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P' \<parallel> Q)"
    by(rule residualEq)
    
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P'" by(rule_tac cPar1) auto
  moreover note \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
                \<open>bn \<alpha> \<sharp>* Q\<close> \<open>distinct(bn \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q)"
    by(rule_tac rPar1)

  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* bn \<alpha>'\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> Q)\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> Q))"
    by(rule_tac rAlpha) auto
  with \<alpha>Eq P'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P \<alpha>' C Q'')
  note \<open>\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> Q''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> Q')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> Q'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and Q'eq: "Q'' = p \<bullet> (P \<parallel> Q')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P \<parallel> Q')"
    by(rule residualEq)
    
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q'" by(rule_tac cPar2) auto

  moreover note \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* C\<close>
                \<open>bn \<alpha> \<sharp>* Q\<close> \<open>distinct(bn \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q')"
    by(rule_tac rPar2)
  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* (bn \<alpha>')\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> Q')\<close>
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> Q'))"
    by(rule_tac rAlpha) auto
  with \<alpha>Eq Q'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac rComm1) (assumption | simp)+
  thus ?case using \<open>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''\<close>
    by(simp add: residualInject)
next
  case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q \<alpha> C P'')
  hence "Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
    by(rule_tac rComm2) (assumption | simp)+
  thus ?case using \<open>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q') = \<alpha> \<prec> P''\<close>
    by(simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec yvec N P' x \<alpha> C P'')
  note \<open>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close>
  moreover from \<open>xvec \<sharp>* \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>yvec \<sharp>* \<alpha>\<close> have "(xvec@x#yvec) \<sharp>* (bn \<alpha>)"
    by auto
  moreover from \<open>xvec \<sharp>* yvec\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
  have "distinct(xvec@x#yvec)"
    by(auto simp add: fresh_star_def) (simp add: fresh_def name_list_supp)
  moreover note \<open>distinct(bn \<alpha>)\<close>
  moreover from \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> M\<close> \<open>yvec \<sharp>* M\<close> have "(xvec@x#yvec) \<sharp>* M" by auto
  hence "(xvec@x#yvec) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by auto
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P'')" by simp
  ultimately obtain p where S: "(set p) \<subseteq> (set(xvec@x#yvec)) \<times> (set(p \<bullet> (xvec@x#yvec)))" and "distinctPerm p"
             and \<alpha>eq: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>" and P'eq: "P'' = (p \<bullet> P')"
             and A: "(xvec@x#yvec) \<sharp>* ((p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>)"
             and B: "(p \<bullet> (xvec@x#yvec)) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)"
             and C: "(p \<bullet> (xvec@x#yvec)) \<sharp>* P'"
    by(rule_tac residualEq) (assumption | simp)+
    
  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<in> (supp N)\<close>

  moreover {
    fix C
    from \<open>xvec \<sharp>* M\<close> \<open>yvec \<sharp>* M\<close> have "(xvec@yvec) \<sharp>* M" by simp
    moreover from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec \<sharp>* yvec\<close> have "distinct(xvec@yvec)"
      by auto (simp add: fresh_star_def name_list_supp fresh_def)
    ultimately have "Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P'" by(rule_tac cOpen) auto
  }

  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* M\<close>
                 \<open>yvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* M\<close> \<open>yvec \<sharp>* C\<close> \<open>x \<sharp> C\<close> \<open>xvec \<sharp>* C\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) P'"
    by(rule_tac rOpen) 

  with \<open>xvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>yvec \<sharp>* P\<close> \<open>xvec \<sharp>* M\<close> \<open>yvec \<sharp>* M\<close> 
       \<open>yvec \<sharp>* C\<close>  S \<open>distinctPerm p\<close> \<open>x \<sharp> C\<close> \<open>xvec \<sharp>* C\<close>
       \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> A B C
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (p \<bullet> (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)) (p \<bullet> P')"
    apply(rule_tac \<alpha>="M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>" in rAlpha)
    apply(assumption | simp)+
    apply(fastforce simp add: fresh_star_def abs_fresh)
    by(assumption | simp)+
  with \<alpha>eq P'eq show ?case by simp
next
  case(cScope \<Psi> P \<alpha> P' x \<alpha>' C P'')
  note \<open>\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P') = \<alpha>' \<prec> P''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (\<lparr>\<nu>x\<rparr>P')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (\<lparr>\<nu>x\<rparr>P')"
    by(rule residualEq)
    
  note \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
  have "\<And>C. Prop C \<Psi> P \<alpha> P'" by(rule_tac cScope) auto

  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
                \<open>x \<sharp> C\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>distinct(bn \<alpha>)\<close>
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P')"
    by(rule rScope) 
  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* (bn \<alpha>')\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (\<lparr>\<nu>x\<rparr>P')\<close>
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (p \<bullet> \<alpha>) (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))"
    by(rule_tac rAlpha) simp+
  with \<alpha>Eq P'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(Bang \<Psi> P Rs \<alpha> C)
  thus ?case by(rule_tac rBang) auto
qed

lemma outputInduct[consumes 1, case_names cOutput cCase cPar1 cPar2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) boundOutput \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>ROut M B"
  and     rOutput: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) K (N \<prec>' P)"
  and     rCase: "\<And>\<Psi> P M B \<phi> Cs C.  
                  \<lbrakk>\<Psi> \<rhd> P \<longmapsto>(ROut M B); \<And>C. Prop C \<Psi> P M B; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                   Prop C \<Psi> (Cases Cs) M B"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q))"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q');
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* P;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q'))"
  and     rOpen:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P')"
  and     rScope: "\<And>\<Psi> P M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P');
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;
                    x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' \<lparr>\<nu>x\<rparr>P')"
  and     rBang:    "\<And>\<Psi> P M B C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>(ROut M B); guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M B\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) M B"
  shows "Prop C \<Psi> P M B"
using \<open>\<Psi> \<rhd> P \<longmapsto>(ROut M B)\<close>
proof(nominal_induct \<Psi> P Rs=="(ROut M B)" avoiding: C arbitrary: B rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P C)
  thus ?case by(simp add: residualInject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(force simp add: residualInject intro: rOutput)
next
  case(Case \<Psi> P Rs \<phi> Cs C)
  thus ?case by(force intro: rCase) 
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q C)
  thus ?case by(force intro: rPar1 simp add: residualInject)
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P C)
  thus ?case by(force intro: rPar2 simp add: residualInject)
next
  case cComm1
  thus ?case by(simp add: residualInject)
next
  case cComm2
  thus ?case by(simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec yvec N P' x C B)
  thus ?case by(force intro: rOpen simp add: residualInject)
next
  case(cScope \<Psi> P M \<alpha> P' x C)
  thus ?case by(force intro: rScope simp add: residualInject)
next
  case(Bang  \<Psi> P Rs C)
  thus ?case by(force intro: rBang)
qed

lemma boundOutputBindObject:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "y \<in> set(bn \<alpha>)"

  shows "y \<in> supp(object \<alpha>)"
using assms
proof(nominal_induct avoiding: P' arbitrary: y rule: semanticsInduct)
  case(cAlpha \<Psi> P \<alpha> P' p P'' y)
  from \<open>y \<in> set(bn(p \<bullet> \<alpha>))\<close> have "(p \<bullet> y) \<in> (p \<bullet> set(bn(p \<bullet> \<alpha>)))"
    by(rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  hence "(p \<bullet> y) \<in> set(bn \<alpha>)" using \<open>distinctPerm p\<close>
    by(simp add: eqvts)
  hence "(p \<bullet> y) \<in> supp(object \<alpha>)" by(rule cAlpha)
  hence "(p \<bullet> p \<bullet> y) \<in> (p \<bullet> supp(object \<alpha>))"
    by(rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  thus ?case using \<open>distinctPerm p\<close>
    by(simp add: eqvts)
next
  case cInput 
  thus ?case by(simp add: supp_list_nil)
next
  case cOutput
  thus ?case by(simp add: supp_list_nil)
next
  case cCase
  thus ?case by simp
next
  case cPar1
  thus ?case by simp
next
  case cPar2
  thus ?case by simp
next
  case cComm1
  thus ?case by(simp add: supp_list_nil)
next
  case cComm2
  thus ?case by(simp add: supp_list_nil)
next
  case cOpen
  thus ?case by(auto simp add: supp_list_cons supp_list_append supp_atm supp_some)
next
  case cScope
  thus ?case by simp
next
  case cBang
  thus ?case by simp
qed

lemma alphaBoundOutputChain':
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   B    :: "('a, 'b, 'c) boundOutput"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* B"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>B = \<lparr>\<nu>*yvec\<rparr>([xvec yvec] \<bullet>\<^sub>v B)"
using assms
proof(induct rule: composePermInduct)
  case cBase
  show ?case by simp
next
  case(cStep x xvec y yvec)
  thus ?case
    apply auto
    by(subst alphaBoundOutput[of y]) (auto simp add: eqvts)
qed

lemma alphaBoundOutputChain'':
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* N"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P) = \<lparr>\<nu>*yvec\<rparr>(([xvec yvec] \<bullet>\<^sub>v N) \<prec>' ([xvec yvec] \<bullet>\<^sub>v P))"
proof -
  from assms have "\<lparr>\<nu>*xvec\<rparr>(N \<prec>' P) = \<lparr>\<nu>*yvec\<rparr>([xvec yvec] \<bullet>\<^sub>v (N \<prec>' P))"
    by(simp add: alphaBoundOutputChain')
  thus ?thesis by simp
qed

lemma alphaDistinct:
  fixes xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   M    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> Q"
  and     "distinct(bn \<alpha>)"
  and     "\<And>x. x \<in> set(bn \<alpha>) \<Longrightarrow> x \<in> supp(object \<alpha>)"
  and     "bn \<alpha> \<sharp>* bn \<beta>"
  and     "bn \<alpha> \<sharp>* (object \<beta>)"
  and     "bn \<alpha> \<sharp>* Q"

  shows "distinct(bn \<beta>)"
using assms
proof(rule_tac actionCases[where \<alpha>=\<alpha>], auto simp add: residualInject supp_some)
  fix xvec M yvec N
  assume Eq: "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*yvec\<rparr>M \<prec>' Q" 
  assume "distinct xvec" and "xvec \<sharp>* M" and "xvec \<sharp>* yvec" and "xvec \<sharp>* Q" 
  assume Mem: "\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> (supp N)"
  show "distinct yvec"
proof -
  from Eq have "length xvec = length yvec"
    by(rule boundOutputChainEqLength)
  with Eq \<open>distinct xvec\<close> \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close> Mem show ?thesis
  proof(induct n=="length xvec" arbitrary: xvec yvec M Q rule: nat.induct)
    case(zero xvec yvec M Q)
    thus ?case by simp
  next
    case(Suc n xvec yvec M Q)
    have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
    then obtain x xvec' y yvec' where xEq: "xvec = x#xvec'" and yEq: "yvec = y#yvec'"
                                  and L': "length xvec' = length yvec'"
      by(cases xvec, auto, cases yvec, auto)
    have xvecFreshyvec: "xvec \<sharp>* yvec" and xvecDist: "distinct xvec" by fact+
    with xEq yEq have xineqy: "x \<noteq> y" and xvec'Freshyvec': "xvec' \<sharp>* yvec'"
                  and xvec'Dist: "distinct xvec'" and xFreshxvec': "x \<sharp> xvec'"
                  and xFreshyvec': "x \<sharp> yvec'" and yFreshxvec': "y \<sharp> xvec'"
      by auto
    have Eq: "\<lparr>\<nu>*xvec\<rparr>N \<prec>' P = \<lparr>\<nu>*yvec\<rparr>M \<prec>' Q" by fact
    with xEq yEq xineqy have Eq': "\<lparr>\<nu>*xvec'\<rparr>N \<prec>' P = \<lparr>\<nu>*([(x, y)] \<bullet> yvec')\<rparr>([(x, y)] \<bullet> M) \<prec>' ([(x, y)] \<bullet> Q)"
      by(simp add: boundOutput.inject alpha eqvts) 
    moreover have Mem:"\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp N" by fact
    with xEq have "\<And>x. x \<in> set xvec' \<Longrightarrow> x \<in> supp N" by simp
    moreover have "xvec \<sharp>* M" by fact
    with xEq xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> M)" by simp
    moreover have xvecFreshQ: "xvec \<sharp>* Q" by fact
    with xEq xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
    moreover have "Suc n = length xvec" by fact
    with xEq have "n = length xvec'" by simp
    moreover from xvec'Freshyvec' xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> yvec')"
      by simp
    moreover from L' have "length xvec' = length([(x, y)] \<bullet> yvec')" by simp
    ultimately have "distinct([(x, y)] \<bullet> yvec')" using xvec'Dist
      by(rule_tac Suc) (assumption | simp)+
    hence "distinct yvec'" by simp
    from Mem xEq have xSuppN: "x \<in> supp N" by simp
    from L \<open>distinct xvec\<close> \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* Q\<close> 
    have "\<lparr>\<nu>*yvec\<rparr>M \<prec>' Q = \<lparr>\<nu>*xvec\<rparr>([yvec xvec] \<bullet>\<^sub>v M) \<prec>' ([yvec xvec] \<bullet>\<^sub>v Q)"
      by(simp add: alphaBoundOutputChain'')
    with Eq have "N = [yvec xvec] \<bullet>\<^sub>v M" by simp
    with xEq yEq have "N = [(y, x)] \<bullet> [yvec' xvec'] \<bullet>\<^sub>v M"
      by simp
    with xSuppN have ySuppM: "y \<in> supp([yvec' xvec'] \<bullet>\<^sub>v M)"
      by(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
        (simp add: calc_atm eqvts name_swap)
    have "y \<sharp> yvec'"
    proof(simp add: fresh_def, rule notI)
      assume "y \<in> supp yvec'"
      hence "y mem yvec'"
        by(induct yvec') (auto simp add: supp_list_nil supp_list_cons supp_atm)
      moreover from \<open>xvec \<sharp>* M\<close> xEq xFreshxvec' have "xvec' \<sharp>* M" by simp
      ultimately have "y \<sharp> [yvec' xvec'] \<bullet>\<^sub>v  M" using L' xvec'Freshyvec' xvec'Dist
        by(force intro: freshChainPerm)
      with ySuppM show "False" by(simp add: fresh_def)
    qed
    with \<open>distinct yvec'\<close>  yEq show ?case by simp
  qed
qed
qed

lemma boundOutputDistinct:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"

  shows "distinct(bn \<alpha>)"
using assms
proof(nominal_induct \<Psi> P x3=="\<alpha> \<prec> P'" avoiding: \<alpha> P' rule: semantics.strong_induct)
  case cInput
  thus ?case by(simp add: residualInject)
next
  case Output
  thus ?case by(simp add: residualInject)
next
  case Case
  thus ?case by(simp add: residualInject)
next
  case cPar1
  thus ?case by(force intro: alphaDistinct boundOutputBindObject)
next
  case cPar2
  thus ?case by(force intro: alphaDistinct boundOutputBindObject)
next 
  case cComm1
  thus ?case by(simp add: residualInject)
next
  case cComm2
  thus ?case by(simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec yvec N P' x \<alpha> P'')
  note \<open>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close>
  moreover from \<open>xvec \<sharp>* yvec\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
  have "distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
    by auto (simp add: fresh_star_def fresh_def name_list_supp)
  moreover {
    fix y
    from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<in> supp N\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> \<Psi>\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* yvec\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* M\<close>
    have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule semantics.cOpen)
    moreover moreover from \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> M\<close> \<open>yvec \<sharp>* M\<close> 
    have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* (subject(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by simp
    moreover note \<open>distinct(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))\<close>
    moreover assume "y \<in> set(bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"

    ultimately have "y \<in> supp(object(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>))"
      by(rule_tac boundOutputBindObject)
  }
  moreover from \<open>xvec \<sharp>* \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>yvec \<sharp>* \<alpha>\<close>
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* bn \<alpha>" and "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* object \<alpha>" by simp+
  moreover from \<open>xvec \<sharp>* P''\<close> \<open>x \<sharp> P''\<close> \<open>yvec \<sharp>* P''\<close>
  have "bn(M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>) \<sharp>* P''" by simp
  ultimately show ?case by(rule alphaDistinct)
next
  case cScope
  thus ?case
    by(rule_tac alphaDistinct, auto) (rule_tac boundOutputBindObject, auto)
next
  case Bang
  thus ?case by simp
qed

lemma inputDistinct:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"

  assumes "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto> Rs"

  shows "distinct xvec"
using assms
by(nominal_induct \<Psi> P=="M\<lparr>\<lambda>*xvec N\<rparr>.P" Rs avoiding: xvec N P rule: semantics.strong_induct)
  (auto simp add: psi.inject intro: alphaInputDistinct)

lemma outputInduct'[consumes 2, case_names cAlpha cOutput cCase cPar1 cPar2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> name list \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     rAlpha: "\<And>\<Psi> P M xvec N P' p C. \<lbrakk>xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M;  xvec \<sharp>* C; xvec \<sharp>* (p \<bullet> xvec); 
                                           set p \<subseteq> set xvec \<times> set(p \<bullet> xvec); distinctPerm p;
                                           (p \<bullet> xvec) \<sharp>* N; (p \<bullet> xvec) \<sharp>* P'; Prop C \<Psi> P M xvec N P'\<rbrakk> \<Longrightarrow>
                                           Prop C \<Psi> P M (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P')"
  and     rOutput: "\<And>\<Psi> M K N P C. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) K ([]) N P"
  and     rCase: "\<And>\<Psi> P M xvec N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M xvec N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                             Prop C \<Psi> (Cases Cs) M xvec N P'"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N  P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M xvec N P';
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; 
                    A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M xvec N (P' \<parallel> Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q M xvec N  Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                    \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M xvec N Q';
                    A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; 
                    A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C; xvec \<sharp>* Q;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) M xvec N (P \<parallel> Q')"
  and     rOpen:  "\<And>\<Psi> P M xvec yvec N P' x C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; \<And>C. Prop C \<Psi> P M (xvec@yvec) N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> yvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; 
                    yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; yvec \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> 
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (xvec@x#yvec) N P'"
  and     rScope: "\<And>\<Psi> P M xvec N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> P M xvec N P';
                    x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* P; xvec \<sharp>* M; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M xvec N (\<lparr>\<nu>x\<rparr>P')"
  and     rBang:    "\<And>\<Psi> P M xvec N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M xvec N P'\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) M xvec N P'"
  shows "Prop C \<Psi> P M xvec N P'"
proof -
  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  moreover from \<open>xvec \<sharp>* M\<close> have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))"
    by(rule boundOutputDistinct)
  ultimately show ?thesis
  proof(nominal_induct \<Psi> P \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: C arbitrary: M xvec N rule: semanticsInduct)
    case(cAlpha \<Psi> P \<alpha> P' p C M xvec N)
    from \<open>(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)"
      by(simp add: fresh_bij)
    with \<open>distinctPerm p\<close> have A: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>"
      by(simp add: eqvts)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha> \<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* bn(p \<bullet> \<alpha>)\<close> \<open>distinctPerm p\<close>
    have "(p \<bullet> xvec) \<sharp>* \<Psi>" and  "(p \<bullet> xvec) \<sharp>* P" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" and  "(p \<bullet> xvec) \<sharp>* C" and  "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> xvec)"
      by auto
    moreover from A \<open>set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))\<close> \<open>distinctPerm p\<close>
    have S: "set p \<subseteq> set(p \<bullet> xvec) \<times> set(p \<bullet> p \<bullet> xvec)" by simp
    moreover note \<open>distinctPerm p\<close>
    moreover from A \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* P'\<close>
    have "(p \<bullet> p \<bullet> xvec) \<sharp>* (p \<bullet> N)" and "(p \<bullet> p \<bullet> xvec) \<sharp>* P'" by simp+
    moreover from A have "Prop C \<Psi> P (p \<bullet> M) (p \<bullet> xvec) (p \<bullet> N) P'"
      by(rule cAlpha)
    ultimately have "Prop C \<Psi> P (p \<bullet> M) (p \<bullet> p \<bullet> xvec) (p \<bullet> p \<bullet> N) (p \<bullet> P')"
      by(rule rAlpha)
    moreover from A \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" by simp
    hence "xvec \<sharp>* M" by(simp add: fresh_star_bij)
    from A \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>distinctPerm p\<close> have "xvec \<sharp>* (p \<bullet> M)" by simp
    hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> M)" by(simp add: fresh_star_bij)
    with \<open>distinctPerm p\<close> have "(p \<bullet> xvec) \<sharp>* M" by simp
    with \<open>xvec \<sharp>* M\<close> S \<open>distinctPerm p\<close> have  "(p \<bullet> M) = M" by simp
    ultimately show ?case using S \<open>distinctPerm p\<close> by simp 
  next
    case cInput
    thus ?case by(simp add: residualInject)
  next
    case cOutput
    thus ?case by(force dest: rOutput simp add: action.inject)
  next
    case cCase
    thus ?case by(force intro: rCase)
  next
    case cPar1
    thus ?case by(force intro: rPar1)
  next
    case cPar2
    thus ?case by(force intro: rPar2)
  next
    case cComm1
    thus ?case by(simp add: action.inject)
  next
    case cComm2
    thus ?case by(simp add: action.inject)
  next
    case cOpen
    thus ?case by(fastforce intro: rOpen simp add: action.inject)
  next
    case cScope
    thus ?case by(fastforce intro: rScope)
  next
    case cBang
    thus ?case by(fastforce intro: rBang)
  qed
qed

lemma inputInduct[consumes 1, case_names cInput cCase cPar1 cPar2 cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     rInput: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec])"
  and     rCase: "\<And>\<Psi> P M N P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P M N P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow>
                                        Prop C \<Psi> (Cases Cs) M N P'" 
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M N P'; distinct A\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P' \<parallel> Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M N Q'; distinct A\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P \<parallel> Q')"
  and     rScope: "\<And>\<Psi> P M N P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<And>C. Prop C \<Psi> P M N P'; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M N (\<lparr>\<nu>x\<rparr>P')"
  and     rBang:    "\<And>\<Psi> P M N P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) M N P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) M N P'"
  shows "Prop C \<Psi> P M N P'"
using Trans
proof(nominal_induct \<Psi> P Rs=="M\<lparr>N\<rparr> \<prec> P'" avoiding: C arbitrary: P' rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P C)
  thus ?case
    by(force intro: rInput simp add: residualInject action.inject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(simp add: residualInject)
next
  case(Case \<Psi> P Rs \<phi> CS C)
  thus ?case by(force intro: rCase)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q C P'')
  thus ?case by(force intro: rPar1 simp add: residualInject)
next 
  case(cPar2 \<Psi> \<Psi>P Q \<alpha> Q' xvec P C Q'')
  thus ?case by(force intro: rPar2 simp add: residualInject)
next
  case(cComm1 \<Psi> \<Psi>Q P M N P' xvec \<Psi>P Q K zvec Q' yvec C PQ)
  thus ?case by(simp add: residualInject)
next
  case(cComm2 \<Psi> \<Psi>Q P M zvec N P' xvec \<Psi>P Q K yvec Q' C PQ)
  thus ?case by(simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec N P' x yvec C P'') 
  thus ?case by(simp add: residualInject)
next
  case(cScope \<Psi> P \<alpha> P' x C P'')
  thus ?case by(force intro: rScope simp add: residualInject)
next
  case(Bang \<Psi> P Rs C)
  thus ?case by(force intro: rBang)
qed

lemma tauInduct[consumes 1, case_names cCase cPar1 cPar2 cComm1 cComm2 cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     rCase: "\<And>\<Psi> P P' \<phi> Cs C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> 
                                    Prop C \<Psi> (Cases Cs) P'"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<tau> \<prec> P'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P P';
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>;
                   A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P' \<parallel> Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<tau> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q Q';
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>;
                   A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P \<parallel> Q')"
  and     rComm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rComm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';  extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; 
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rScope: "\<And>\<Psi> P P' x C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'; \<And>C. Prop C \<Psi> P P'; x \<sharp> \<Psi>; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<lparr>\<nu>x\<rparr>P')"
  and     rBang:    "\<And>\<Psi> P P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<tau> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P'"
  shows "Prop C \<Psi> P P'"
using Trans
proof(nominal_induct \<Psi> P Rs=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: semantics.strong_induct)
  case(cInput M K xvec N Tvec P C)
  thus ?case by(simp add: residualInject)
next
  case(Output \<Psi> M K N P C)
  thus ?case by(simp add: residualInject)
next
  case(Case \<Psi> P Rs \<phi> Cs C)
  thus ?case by(force intro: rCase simp add: residualInject)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q C P'')
  thus ?case by(force intro: rPar1 simp add: residualInject)
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P C Q'')
  thus ?case by(force intro: rPar2 simp add: residualInject)
next
  case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C PQ)
  thus ?case by(force intro: rComm1 simp add: residualInject)
next
  case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>P Q' A\<^sub>Q C PQ)
  thus ?case by(force intro: rComm2 simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec N P' x yvec C P'')
  thus ?case by(simp add: residualInject)
next
  case(cScope \<Psi> P \<alpha> P' x C P'')
  thus ?case by(force intro: rScope simp add: residualInject)
next
  case(Bang \<Psi> P Rs C )
  thus ?case by(force intro: rBang simp add: residualInject)
qed

lemma semanticsFrameInduct[consumes 3, case_names cAlpha cInput cOutput cCase cPar1 cPar2 cComm1 cComm2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) residual \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto> Rs"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     rAlpha: "\<And>\<Psi> P A\<^sub>P \<Psi>\<^sub>P p Rs C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* C;
                                         set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinctPerm p;
                                          Prop C \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P Rs (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     rInput: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              (K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (P[xvec::=Tvec])) ([]) (\<one>)"
  and     rOutput: "\<And>\<Psi> M K N P C. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (K\<langle>N\<rangle> \<prec> P) ([]) (\<one>)"
  and     rCase: "\<And>\<Psi> P Rs \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto> Rs; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) Rs ([]) (\<one>)"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P; distinct(bn \<alpha>);
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q; distinct(bn \<alpha>);
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P ((M\<lparr>N\<rparr>) \<prec> P') A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>N\<rparr> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rOpen: "\<And>\<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec; xvec \<sharp>* yvec; distinct xvec; distinct yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; yvec \<sharp>* \<Psi>\<^sub>P;
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rScope: "\<And>\<Psi> P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P;
                     x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; distinct(bn \<alpha>);
                     bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rBang:    "\<And>\<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs; guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) Rs A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Rs; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) Rs ([]) (\<one>)"
  shows "Prop C \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP \<open>distinct A\<^sub>P\<close>
proof(nominal_induct  avoiding: A\<^sub>P \<Psi>\<^sub>P C rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P A\<^sub>P \<Psi>\<^sub>P C)
  from \<open>extractFrame (M\<lparr>\<lambda>*xvec N\<rparr>.P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
  have "A\<^sub>P = []" and "\<Psi>\<^sub>P = \<one>"
    by auto
  with \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
       \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* K\<close> \<open>xvec \<sharp>* C\<close>
  show ?case by(blast intro: rInput)
next
  case(Output \<Psi> M K N P A\<^sub>P \<Psi>\<^sub>P)
  from \<open>extractFrame (M\<langle>N\<rangle>.P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
  have "A\<^sub>P = []" and "\<Psi>\<^sub>P = \<one>"
    by auto
  with \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> show ?case
    by(blast intro: rOutput)
next
  case(Case \<Psi> P Rs \<phi> Cs A\<^sub>c\<^sub>P \<Psi>\<^sub>c\<^sub>P C)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, Rs, C)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Rs" and "A\<^sub>P \<sharp>* C"
    by simp+
  note \<open>\<Psi> \<rhd> P \<longmapsto> Rs\<close> FrP \<open>distinct A\<^sub>P\<close>
  moreover from FrP \<open>distinct A\<^sub>P\<close> \<open>\<And>A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P\<close> 
  have "\<And>C. Prop C \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P" by simp
  moreover note \<open>(\<phi>, P) mem Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
  moreover from \<open>guarded P\<close> FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)" by(metis guardedStatEq)+
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Rs\<close> \<open>A\<^sub>P \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (Cases Cs) Rs ([]) (\<one>)"
    by(rule rCase)
  thus ?case using \<open>extractFrame(Cases Cs) = \<langle>A\<^sub>c\<^sub>P, \<Psi>\<^sub>c\<^sub>P\<rangle>\<close> by simp
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, \<alpha>, P', A\<^sub>Q, A\<^sub>P\<^sub>Q, C, \<Psi>\<^sub>Q)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* P'"
    and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by simp+

  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> FrP have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+
  
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close> FrQ \<open>distinct A\<^sub>Q\<close>

  moreover from FrP \<open>distinct A\<^sub>P\<close> \<open>\<And>A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P" by simp

  moreover note \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close>
                \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>distinct(bn \<alpha>)\<close>
                \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>  \<open>bn \<alpha> \<sharp>* Q\<close>  \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> 
                \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rPar1)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* C\<close>
       \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
       S \<open>distinctPerm p\<close> Aeq
  have "Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P' \<parallel> Q)) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q))"
    by(rule_tac rAlpha) (assumption | simp add: eqvts)+
  with \<Psi>eq Aeq show ?case by(simp add: eqvts)
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C)
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, \<alpha>, Q', A\<^sub>P, A\<^sub>P\<^sub>Q, C, \<Psi>\<^sub>P)"
    by(rule freshFrame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>Q \<sharp>* Q'"
    and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* C" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  from \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* A\<^sub>Q" by simp
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)
  from \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> FrQ have "bn \<alpha> \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = ((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> FrP \<open>distinct A\<^sub>P\<close> FrQ \<open>distinct A\<^sub>Q\<close>

  moreover from FrQ \<open>distinct A\<^sub>Q\<close> \<open>\<And>A\<^sub>Q \<Psi>\<^sub>Q C. \<lbrakk>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q\<rbrakk> \<Longrightarrow> Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (\<alpha> \<prec> Q') A\<^sub>Q \<Psi>\<^sub>Q" by simp

  moreover note \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close>
                \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>distinct(bn \<alpha>)\<close>
                \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>  \<open>bn \<alpha> \<sharp>* Q\<close>  \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> 
                \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rPar2)

  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* C\<close>
       \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
       S \<open>distinctPerm p\<close> Aeq
  have "Prop C \<Psi> (P \<parallel> Q) (\<alpha> \<prec> (P \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q))"
    by(rule_tac rAlpha) (assumption | simp add: eqvts)+
  with \<Psi>eq Aeq show ?case by(simp add: eqvts)
next
  case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C)
  from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  from cComm1 have  "Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rComm1)
  moreover from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
                \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  with \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct(A\<^sub>P@A\<^sub>Q)\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
  obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinctPerm p"
             and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = p \<bullet> (A\<^sub>P@A\<^sub>Q)"
    by(rule_tac frameChainEq') (assumption | simp)+
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
                \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close>
                \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q))"
    by(rule_tac rAlpha) auto
  with \<Psi>eq Aeq show ?case by simp
next
  case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q A\<^sub>P\<^sub>Q \<Psi>\<^sub>P\<^sub>Q C)
  from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  from cComm2 have  "Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rComm2)
  moreover from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
                \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
    by simp
  with \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct(A\<^sub>P@A\<^sub>Q)\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
  obtain p where S: "(set p \<subseteq> (set(A\<^sub>P@A\<^sub>Q)) \<times> (set A\<^sub>P\<^sub>Q))"  and "distinctPerm p"
             and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = p \<bullet> (A\<^sub>P@A\<^sub>Q)"
    by(rule_tac frameChainEq') (assumption | simp)+
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
                \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close>
                \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (p \<bullet> (A\<^sub>P@A\<^sub>Q)) (p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q))"
    by(rule_tac rAlpha) auto
  with \<Psi>eq Aeq show ?case by simp
next
  case(cOpen \<Psi> P M xvec yvec N P' x A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P C)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, M, xvec, yvec, N, P', A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P, C, x)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* xvec"and "A\<^sub>P \<sharp>* yvec" and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* P'"
    and "A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* C" and "x \<sharp> A\<^sub>P"
    by simp+

  from \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> FrP have "xvec \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)
  from \<open>yvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> FrP have "yvec \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>\<close> FrP
  have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>"
    by simp
  moreover from \<open>x \<sharp> A\<^sub>P\<close> \<open>distinct A\<^sub>P\<close> have "distinct(x#A\<^sub>P)" by simp
  ultimately obtain p where S: "set p \<subseteq> set (x#A\<^sub>P) \<times> set (p \<bullet> (x#A\<^sub>P))" and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>x\<^sub>P = p \<bullet> \<Psi>\<^sub>P" and Aeq: "A\<^sub>x\<^sub>P = (p \<bullet> x)#(p \<bullet> A\<^sub>P)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close>\<open>x \<sharp> A\<^sub>x\<^sub>P\<close> \<open>distinct A\<^sub>x\<^sub>P\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close>
  moreover from FrP \<open>distinct A\<^sub>P\<close> \<open>\<And>A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P\<close>
  have "\<And>C. Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P') A\<^sub>P \<Psi>\<^sub>P" by simp
  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<in> supp N\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* P'\<close>
                \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close>  \<open>xvec \<sharp>* M\<close>  \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close>  \<open>yvec \<sharp>* M\<close>  \<open>yvec \<sharp>* \<Psi>\<^sub>P\<close> 
                \<open>A\<^sub>P \<sharp>* C\<close> \<open>x \<sharp> C\<close> \<open>xvec \<sharp>* C\<close> \<open>yvec \<sharp>* C\<close> \<open>xvec \<sharp>* yvec\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac rOpen)
  
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>x \<sharp> A\<^sub>x\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close> \<open>x \<sharp> A\<^sub>P\<close>
       \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> C\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> Aeq
       S \<open>distinctPerm p\<close>
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P') (p \<bullet> (x#A\<^sub>P)) (p \<bullet> \<Psi>\<^sub>P)"
    by(rule_tac A\<^sub>P="x#A\<^sub>P" in rAlpha) (assumption | simp add: abs_fresh fresh_star_def boundOutputFresh)+
  with \<Psi>eq Aeq show ?case by(simp add: eqvts)
next
  case(cScope \<Psi> P \<alpha> P' x A\<^sub>x\<^sub>P \<Psi>\<^sub>x\<^sub>P C)
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, \<alpha>, P', A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P, C, x)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* P'"
    and "A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>x\<^sub>P" and "A\<^sub>P \<sharp>* C" and "x \<sharp> A\<^sub>P"
    by simp+

  from \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> FrP have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(\<lparr>\<nu>x\<rparr>P) = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>\<close> FrP
  have "\<langle>(x#A\<^sub>P), \<Psi>\<^sub>P\<rangle> = \<langle>A\<^sub>x\<^sub>P, \<Psi>\<^sub>x\<^sub>P\<rangle>"
    by simp
  moreover from \<open>x \<sharp> A\<^sub>P\<close> \<open>distinct A\<^sub>P\<close> have "distinct(x#A\<^sub>P)" by simp
  ultimately obtain p where S: "set p \<subseteq> set (x#A\<^sub>P) \<times> set (p \<bullet> (x#A\<^sub>P))" and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>x\<^sub>P = p \<bullet> \<Psi>\<^sub>P" and Aeq: "A\<^sub>x\<^sub>P = (p \<bullet> x)#(p \<bullet> A\<^sub>P)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close>\<open>x \<sharp> A\<^sub>x\<^sub>P\<close> \<open>distinct A\<^sub>x\<^sub>P\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  note \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close>
  moreover from FrP \<open>distinct A\<^sub>P\<close> \<open>\<And>A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P\<close>
  have "\<And>C. Prop C \<Psi> P (\<alpha> \<prec> P') A\<^sub>P \<Psi>\<^sub>P" by simp
  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>distinct(bn \<alpha>)\<close>
                \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>  \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>x \<sharp> C\<close> \<open>bn \<alpha> \<sharp>* C\<close> 
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac rScope)
  
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>x \<sharp> A\<^sub>x\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>x\<^sub>P\<close> \<open>x \<sharp> A\<^sub>P\<close>
       \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> C\<close> Aeq
       S \<open>distinctPerm p\<close>
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P')) (p \<bullet> (x#A\<^sub>P)) (p \<bullet> \<Psi>\<^sub>P)"
    by(rule_tac A\<^sub>P="x#A\<^sub>P" in rAlpha) (assumption | simp add: abs_fresh fresh_star_def)+
  with \<Psi>eq Aeq show ?case by(simp add: eqvts)
next
  case(Bang \<Psi> P Rs A\<^sub>b\<^sub>P \<Psi>\<^sub>b\<^sub>P C)

  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                  and "A\<^sub>P \<sharp>* (\<Psi>, P, Rs, C)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Rs" and "A\<^sub>P \<sharp>* C" 
    by simp+

  note \<open>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs\<close> \<open>guarded P\<close> FrP \<open>distinct A\<^sub>P\<close>
  moreover from FrP have "extractFrame (P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by simp
  with \<open>distinct A\<^sub>P\<close> \<open>\<And>A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>extractFrame (P \<parallel> !P) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) Rs A\<^sub>P \<Psi>\<^sub>P\<close>
  have "\<And>C. Prop C \<Psi> (P \<parallel> !P) Rs A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>)" by simp
  moreover from \<open>guarded P\<close> FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)" by(metis guardedStatEq)+
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Rs\<close> \<open>A\<^sub>P \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (!P) Rs ([]) (\<one>)"
    by(rule rBang) 
  thus ?case using \<open>extractFrame(!P) = \<langle>A\<^sub>b\<^sub>P, \<Psi>\<^sub>b\<^sub>P\<rangle>\<close> by simp
qed

lemma semanticsFrameInduct'[consumes 5, case_names cAlpha cFrameAlpha cInput cOutput cCase cPar1 cPar2 cComm1 cComm2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a action \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     rAlpha: "\<And>\<Psi> P \<alpha> P' p A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P;
                                           bn \<alpha> \<sharp>* C; bn \<alpha> \<sharp>* (p \<bullet> \<alpha>); A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C;
                                           set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinctPerm p;
                                           bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow>
                                           Prop C \<Psi> P (p \<bullet> \<alpha>) (p \<bullet> P') A\<^sub>P \<Psi>\<^sub>P"
  and     rFrameAlpha: "\<And>\<Psi> P A\<^sub>P \<Psi>\<^sub>P p \<alpha> P' C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C;
                                                set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinctPerm p; A\<^sub>P \<sharp>* subject \<alpha>;
                                                Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P \<alpha> P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     rInput: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              (K\<lparr>(N[xvec::=Tvec])\<rparr>) (P[xvec::=Tvec]) ([]) (\<one>)"
  and     rOutput: "\<And>\<Psi> M K N P C. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) (K\<langle>N\<rangle>) P ([]) (\<one>)"
  and     rCase: "\<And>\<Psi> P \<alpha> P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) \<alpha> P' ([]) (\<one>)"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q' A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>N\<rparr>) P' A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q' A\<^sub>Q \<Psi>\<^sub>Q;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>N\<rparr>) Q' A\<^sub>Q \<Psi>\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rOpen: "\<And>\<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P y C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec; xvec \<sharp>* yvec; distinct xvec; distinct yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; 
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C;
                     y \<noteq> x; y \<sharp> \<Psi>; y \<sharp> P; y \<sharp> M; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> N; y \<sharp> P'; y \<sharp> A\<^sub>P; y \<sharp> \<Psi>\<^sub>P; y \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>) ([(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rScope: "\<And>\<Psi> P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P;
                     x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P';
                     bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; bn \<alpha> \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rBang:    "\<And>\<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'; guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) \<alpha> P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) \<alpha> P' ([]) (\<one>)"
  shows "Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP \<open>distinct A\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
proof(nominal_induct \<Psi> P Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P avoiding: C \<alpha> P' rule: semanticsFrameInduct)
  case cAlpha 
  thus ?case using rFrameAlpha
    by auto
next
  case cInput
  thus ?case using rInput
    by(auto simp add: residualInject)
next
  case cOutput
  thus ?case using rOutput
    by(auto simp add: residualInject)
next
  case cCase
  thus ?case using rCase
    by(auto simp add: residualInject)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C \<alpha>' P'')
  note \<open>\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> P''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> Q)" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (P' \<parallel> Q)" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P' \<parallel> Q)"
    by(rule residualEq)
    
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P" by(rule_tac cPar1) auto

  moreover note \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* C\<close>
                \<open>bn \<alpha> \<sharp>* Q\<close> \<open>distinct(bn \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close>
                \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rPar1)
  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* (bn \<alpha>')\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> Q)\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<alpha>Eq \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rAlpha) auto
  with \<alpha>Eq P'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C \<alpha>' Q'')
  note \<open>\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> Q''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> Q')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> Q'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and Q'eq: "Q'' = p \<bullet> (P \<parallel> Q')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (P \<parallel> Q')"
    by(rule residualEq)
    
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
  have "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q \<alpha> Q' A\<^sub>Q \<Psi>\<^sub>Q" by(rule_tac cPar2) auto

  moreover note \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* C\<close>
                \<open>bn \<alpha> \<sharp>* Q\<close> \<open>distinct(bn \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close>
                \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close>
  ultimately have "Prop C \<Psi> (P \<parallel> Q) \<alpha> (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
    by(rule_tac rPar2) auto
  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* (bn \<alpha>')\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> Q')\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<alpha>Eq \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
  have "Prop C \<Psi> (P \<parallel> Q) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
   by(rule_tac rAlpha) auto
  with \<alpha>Eq Q'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C \<alpha> P'')
  thus ?case using rComm1
    apply(auto)
    apply(drule_tac x="M\<lparr>N\<rparr>" in meta_spec)
    apply(drule_tac x="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" in meta_spec)
    apply(drule_tac x=P' in meta_spec)
    apply(drule_tac x=Q' in meta_spec)
    apply auto
    apply(drule_tac x=\<Psi> in meta_spec)
    apply(drule_tac x=\<Psi>\<^sub>Q in meta_spec)
    apply(drule_tac x=P in meta_spec)
    apply(drule_tac x=M in meta_spec)
    apply(drule_tac x=N in meta_spec)
    apply(drule_tac x=P' in meta_spec)
    apply(drule_tac x=A\<^sub>P in meta_spec)
    apply(drule_tac x=\<Psi>\<^sub>P in meta_spec)
    apply(drule_tac x=Q in meta_spec)
    apply(drule_tac x=K in meta_spec)
    apply(drule_tac x=xvec in meta_spec)
    apply(drule_tac x=Q' in meta_spec)
    apply(drule_tac x=A\<^sub>Q in meta_spec)
    apply auto
    apply(subgoal_tac "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) Q' A\<^sub>Q \<Psi>\<^sub>Q")
    apply(subgoal_tac "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>N\<rparr>) P' A\<^sub>P \<Psi>\<^sub>P")
    by(auto simp add: residualInject)
next
  case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C \<alpha> Q'')
  thus ?case using rComm2
    apply(drule_tac x="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" in meta_spec)
    apply(drule_tac x="K\<lparr>N\<rparr>" in meta_spec)
    apply(drule_tac x=P' in meta_spec)
    apply(drule_tac x=Q' in meta_spec)
    apply auto
    apply(drule_tac x=\<Psi> in meta_spec)
    apply(drule_tac x=\<Psi>\<^sub>Q in meta_spec)
    apply(drule_tac x=P in meta_spec)
    apply(drule_tac x=M in meta_spec)
    apply(drule_tac x=xvec in meta_spec)
    apply(drule_tac x=N in meta_spec)
    apply(drule_tac x=P' in meta_spec)
    apply(drule_tac x=A\<^sub>P in meta_spec)
    apply(drule_tac x=\<Psi>\<^sub>P in meta_spec)
    apply(drule_tac x=Q in meta_spec)
    apply(drule_tac x=K in meta_spec)
    apply(drule_tac x=Q' in meta_spec)
    apply(drule_tac x=A\<^sub>Q in meta_spec)
    apply auto
    apply(subgoal_tac "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P")
    apply(subgoal_tac "\<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q (K\<lparr>N\<rparr>) Q' A\<^sub>Q \<Psi>\<^sub>Q")
    by(auto simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C \<alpha> P'')
  note \<open>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close>
  moreover from \<open>xvec \<sharp>* \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>yvec \<sharp>* \<alpha>\<close> have "(xvec@x#yvec) \<sharp>* (bn \<alpha>)"
    by auto
  moreover from \<open>xvec \<sharp>* yvec\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
  have "distinct(xvec@x#yvec)"
    by(auto simp add: fresh_star_def) (simp add: fresh_def name_list_supp)
  moreover note \<open>distinct(bn \<alpha>)\<close>
  moreover from \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> M\<close> \<open>yvec \<sharp>* M\<close> have "(xvec@x#yvec) \<sharp>* M" by auto
  hence "(xvec@x#yvec) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by auto
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P'')" by simp
  ultimately obtain p where S: "(set p) \<subseteq> (set(xvec@x#yvec)) \<times> (set(p \<bullet> (xvec@x#yvec)))" and "distinctPerm p"
             and \<alpha>eq: "\<alpha> = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>" and P'eq: "P'' = (p \<bullet> P')"
             and A: "(xvec@x#yvec) \<sharp>* ((p \<bullet> M)\<lparr>\<nu>*(p \<bullet> (xvec@x#yvec))\<rparr>\<langle>(p \<bullet> N)\<rangle>)"
             and B: "(p \<bullet> (xvec@x#yvec)) \<sharp>* (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle>)"
             and C: "(p \<bullet> (xvec@x#yvec)) \<sharp>* P'"
    by(rule_tac residualEq) (assumption | simp)+

  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>x \<in> (supp N)\<close>

  moreover {
    fix C
    from \<open>xvec \<sharp>* M\<close> \<open>yvec \<sharp>* M\<close> have "(xvec@yvec) \<sharp>* M" by simp
    moreover from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec \<sharp>* yvec\<close> have "distinct(xvec@yvec)"
      by auto (simp add: fresh_star_def name_list_supp fresh_def) 
    ultimately have "Prop C \<Psi> P (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle>) P' A\<^sub>P \<Psi>\<^sub>P" using \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
      by(rule_tac cOpen) auto
  }
  moreover obtain y::name where "y \<sharp> \<Psi>" and "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> xvec" and "y \<sharp> yvec" and "y \<sharp> \<alpha>" and "y \<sharp> P'" and "y \<sharp> A\<^sub>P" and "y \<sharp> \<Psi>\<^sub>P" and "y \<sharp> M" and "y \<sharp> N" and "y \<sharp> C" and "y \<sharp> p"
    by(generate_fresh "name") auto
  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* M\<close>
                 \<open>yvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec \<sharp>* M\<close> \<open>yvec \<sharp>* C\<close> \<open>x \<sharp> C\<close> \<open>xvec \<sharp>* C\<close> \<open>distinct xvec\<close> \<open>distinct yvec\<close>
                 \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close>
                 \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* C\<close> 
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>) ([(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac rOpen)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> M) = [(x, y)] \<bullet> p \<bullet> M"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<sharp> M\<close> \<open>x \<sharp> \<alpha>\<close> \<alpha>eq \<open>y \<sharp> p\<close> \<open>x \<sharp> M\<close> have D: "(([(x, y)] \<bullet> p) \<bullet> M) = p \<bullet> M"
    by(auto simp add: eqvts freshChainSimps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> xvec) = [(x, y)] \<bullet> p \<bullet> xvec"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<sharp> xvec\<close> \<open>x \<sharp> \<alpha>\<close> \<alpha>eq \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec\<close> have E: "(([(x, y)] \<bullet> p) \<bullet> xvec) = p \<bullet> xvec"
    by(auto simp add: eqvts freshChainSimps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> yvec) = [(x, y)] \<bullet> p \<bullet> yvec"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<sharp> yvec\<close> \<open>x \<sharp> \<alpha>\<close> \<alpha>eq \<open>y \<sharp> p\<close> \<open>x \<sharp> yvec\<close> have F: "(([(x, y)] \<bullet> p) \<bullet> yvec) = p \<bullet> yvec"
    by(auto simp add: eqvts freshChainSimps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> x) = [(x, y)] \<bullet> p \<bullet> x"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<noteq> x\<close> \<open>y \<sharp> p\<close> have G: "(([(x, y)] \<bullet> p) \<bullet> y) = p \<bullet> x"
    apply(simp add: freshChainSimps calc_atm)
    apply(subgoal_tac "y \<noteq> p \<bullet> x")
    apply(clarsimp)
    using A \<alpha>eq
    apply(simp add: eqvts)
    apply(subst fresh_atm[symmetric])
    apply(simp only: freshChainSimps)
    by simp
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> N"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<sharp> N\<close> \<open>x \<sharp> \<alpha>\<close> \<open>y \<sharp> p\<close> \<alpha>eq have H: "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> N) = p \<bullet> N"
    by(auto simp add: eqvts freshChainSimps)
  moreover have "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') = [(x, y)] \<bullet> p \<bullet> P'"
    by(subst perm_compose[symmetric]) simp
  with \<open>y \<sharp> P'\<close> \<open>x \<sharp> P''\<close> \<open>y \<sharp> p\<close> P'eq have I: "(([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') = p \<bullet> P'"
    by(auto simp add: eqvts freshChainSimps)
  from \<open>y \<sharp> p\<close> \<open>y \<noteq> x\<close> have "y \<noteq> p \<bullet> x"
    apply(subst fresh_atm[symmetric])
    apply(simp only: freshChainSimps)
    by simp
  moreover from S have "([(x, y)] \<bullet> set p) \<subseteq> [(x, y)] \<bullet> (set(xvec@x#yvec) \<times> set(p \<bullet> (xvec@x#yvec)))"
    by(simp)
  with \<open>y \<noteq> p \<bullet> x\<close> \<open>(([(x, y)] \<bullet> p) \<bullet> y) = p \<bullet> x\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>y \<sharp> yvec\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> \<alpha>\<close> \<alpha>eq have 
    "set([(x, y)] \<bullet> p) \<subseteq> set(xvec@y#yvec) \<times> set(([(x, y)] \<bullet> p) \<bullet> (xvec@y#yvec))"
    by(simp add: eqvts calc_atm perm_compose)
  moreover note \<open>xvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>yvec \<sharp>* P\<close> \<open>xvec \<sharp>* M\<close> \<open>yvec \<sharp>* M\<close> 
                \<open>yvec \<sharp>* C\<close>  S \<open>distinctPerm p\<close> \<open>x \<sharp> C\<close> \<open>xvec \<sharp>* C\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>yvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>x \<sharp> \<Psi>\<close>
                \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* N\<close>
                 A B C  \<alpha>eq \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> \<Psi>\<^sub>P\<close> \<open>y \<sharp> C\<close> \<open>xvec \<sharp>* \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>yvec \<sharp>* \<alpha>\<close> \<open>y \<sharp> \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>y \<sharp> A\<^sub>P\<close> \<open>y \<sharp> N\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>y \<sharp> P'\<close> \<open>A\<^sub>P \<sharp>* C\<close> P'eq
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (([(x, y)] \<bullet> p) \<bullet> (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>)) (([(x, y)] \<bullet> p) \<bullet> [(x, y)] \<bullet> P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    apply(rule_tac \<alpha>="M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle>" in rAlpha)
    apply(assumption | simp)+
    apply(simp add: eqvts)
    apply(assumption | simp add: abs_fresh)+
    apply(simp add: fresh_left calc_atm)
    apply(assumption | simp)+
    apply(simp add: fresh_left calc_atm)
    apply(assumption | simp)+
    by(simp add: eqvts fresh_left)+
  with \<alpha>eq P'eq D E F G H I show ?case 
    by(simp add: eqvts)
next    
 case(cScope \<Psi> P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C \<alpha>' P'')
  note \<open>\<alpha> \<prec> (\<lparr>\<nu>x\<rparr>P') = \<alpha>' \<prec> P''\<close>
  moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* (bn \<alpha>')" by auto
  moreover note \<open>distinct (bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
  have "bn \<alpha> \<sharp>* (\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P')" and "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp+
  ultimately obtain p where S: "(set p) \<subseteq> (set(bn \<alpha>)) \<times> (set(bn(p \<bullet> \<alpha>)))" and "distinctPerm p"
                        and \<alpha>Eq: "\<alpha>' = p \<bullet> \<alpha>" and P'eq: "P'' = p \<bullet> (\<lparr>\<nu>x\<rparr>P')" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>"
                        and "(bn(p \<bullet> \<alpha>)) \<sharp>* (\<lparr>\<nu>x\<rparr>P')"
    by(rule residualEq)
    
  note \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close>
  moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
  have "\<And>C. Prop C \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P" by(rule_tac cScope) auto

  moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close>
                \<open>x \<sharp> C\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>distinct(bn \<alpha>)\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
                \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* C\<close>
  ultimately have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) \<alpha> (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
    by(rule_tac rScope) 
  with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>bn \<alpha> \<sharp>* (bn \<alpha>')\<close> S \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (\<lparr>\<nu>x\<rparr>P')\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<alpha>Eq \<open>x \<sharp> \<alpha>'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>x \<sharp> C\<close> \<open>A\<^sub>P \<sharp>* C\<close>
  have "Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (p \<bullet> \<alpha>) (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))  (x#A\<^sub>P) \<Psi>\<^sub>P" 
    by(rule_tac rAlpha) (simp add: abs_fresh)+
  with \<alpha>Eq P'eq \<open>distinctPerm p\<close> show ?case by simp
next
  case(cBang \<Psi> P Rs A\<^sub>P \<Psi>\<^sub>P C \<alpha>)
  thus ?case by(rule_tac rBang) auto 
qed

lemma inputFrameInduct[consumes 3, case_names cAlpha cInput cCase cPar1 cPar2 cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     rAlpha: "\<And>\<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* C;
                                            set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinctPerm p;
                                             Prop C \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P M N P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     rInput: "\<And>\<Psi> M K xvec N Tvec P C.
                   \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N;
                    length xvec = length Tvec; xvec \<sharp>* \<Psi>;
                    xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (M\<lparr>\<lambda>*xvec N\<rparr>.P)
                              K (N[xvec::=Tvec]) (P[xvec::=Tvec]) ([]) (\<one>)"
  and     rCase: "\<And>\<Psi> P M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P;
                                              (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                              A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) M N P' ([]) (\<one>)"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M N P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M N Q' A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M N (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rScope: "\<And>\<Psi> P M N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P; x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> N; 
                     x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* C; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M N (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rBang:    "\<And>\<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) M N P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) M N P' ([]) (\<one>)"
  shows "Prop C \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P"
using assms
by(nominal_induct \<Psi> P Rs=="M\<lparr>N\<rparr> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P avoiding: C arbitrary: P' rule: semanticsFrameInduct)
  (auto simp add: residualInject)

lemma outputFrameInduct[consumes 3, case_names cAlpha cOutput cCase cPar1 cPar2 cOpen cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 'a \<Rightarrow> ('a, 'b, 'c) boundOutput \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>ROut M B"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     rAlpha: "\<And>\<Psi> P M A\<^sub>P \<Psi>\<^sub>P p B C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* C;
                                         set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P); distinctPerm p;
                                          Prop C \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P M B (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     rOutput: "\<And>\<Psi> M K N P C. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop C \<Psi> (M\<langle>N\<rangle>.P) K (N \<prec>' P) ([]) (\<one>)"
  and     rCase: "\<And>\<Psi> P M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>(ROut M B); extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P;
                                            (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                            A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* B; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) M B ([]) (\<one>)"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> Q)) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q M xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q') A\<^sub>Q \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* Q; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rOpen: "\<And>\<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*(xvec@yvec)\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P; x \<in> supp N; x \<sharp> \<Psi>; x \<sharp> M;
                     x \<sharp> A\<^sub>P; x \<sharp> xvec; x \<sharp> yvec; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* yvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P; 
                     yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rScope: "\<And>\<Psi> P M xvec N P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P') A\<^sub>P \<Psi>\<^sub>P;
                     x \<sharp> \<Psi>; x \<sharp> M; x \<sharp> xvec; x \<sharp> N; x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;
                     A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* xvec;
                     xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* \<Psi>\<^sub>P;
                     A\<^sub>P \<sharp>* C; x \<sharp> C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (\<lparr>\<nu>x\<rparr>P')) (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rBang:    "\<And>\<Psi> P M B A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>ROut M B; guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) M B A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) M B ([]) (\<one>)"
  shows "Prop C \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P"
proof -
  {
    fix B
    assume "\<Psi> \<rhd> P \<longmapsto>ROut M B"
    hence "Prop C \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P" using FrP \<open>distinct A\<^sub>P\<close>
    proof(nominal_induct \<Psi> P Rs=="ROut M B" A\<^sub>P \<Psi>\<^sub>P avoiding: C arbitrary: B rule: semanticsFrameInduct)
      case cAlpha
      thus ?case by(fastforce intro: rAlpha) 
    next
      case cInput 
      thus ?case by(simp add: residualInject)
    next
      case cOutput
      thus ?case by(force intro: rOutput simp add: residualInject)
    next
      case cCase
      thus ?case by(force intro: rCase simp add: residualInject)
    next
      case cPar1
      thus ?case
        by(fastforce intro: rPar1 simp add: residualInject)
    next
      case cPar2
      thus ?case
        by(fastforce intro: rPar2 simp add: residualInject)
    next
      case cComm1
      thus ?case by(simp add: residualInject)
    next
      case cComm2
      thus ?case by(simp add: residualInject)
    next
      case cOpen
      thus ?case by(fastforce intro: rOpen simp add: residualInject)
    next
      case cScope
      thus ?case by(force intro: rScope simp add: residualInject)
    next
      case cBang
      thus ?case by(force intro: rBang simp add: residualInject)
    qed
  }
  with Trans show ?thesis by(simp add: residualInject)
qed

lemma tauFrameInduct[consumes 3, case_names cAlpha cCase cPar1 cPar2 cComm1 cComm2 cScope cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                 ('a, 'b, 'c) psi \<Rightarrow> name list \<Rightarrow> 'b \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     rAlpha: "\<And>\<Psi> P P' A\<^sub>P \<Psi>\<^sub>P p C. \<lbrakk>A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* (p \<bullet> A\<^sub>P); A\<^sub>P \<sharp>* C;
                                        set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P); distinctPerm p;
                                         Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P\<rbrakk> \<Longrightarrow> Prop C \<Psi> P P' (p \<bullet> A\<^sub>P) (p \<bullet> \<Psi>\<^sub>P)"
  and     rCase: "\<And>\<Psi> P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P; \<And>C. Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P;
                                          (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P;  \<Psi>\<^sub>P \<simeq> \<one>; (supp \<Psi>\<^sub>P) = ({}::name set);
                                          A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (Cases Cs) P' ([]) (\<one>)"
  and     rPar1: "\<And>\<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<tau> \<prec> P';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>Q) P P' A\<^sub>P \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P' \<parallel> Q) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rPar2: "\<And>\<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<tau> \<prec> Q';
                   extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                   extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                   \<And>C. Prop C (\<Psi> \<otimes> \<Psi>\<^sub>P) Q Q' A\<^sub>Q \<Psi>\<^sub>Q; 
                   A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;
                   A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                   A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow>
                   Prop C \<Psi> (P \<parallel> Q) (P \<parallel> Q') (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm1: "\<And>\<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rComm2: "\<And>\<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C.
                   \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
                    A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* P'; 
                    A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; 
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* Q';
                    A\<^sub>Q \<sharp>* xvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; 
                    xvec \<sharp>* Q; xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> Q) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) (A\<^sub>P@A\<^sub>Q) (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)"
  and     rScope: "\<And>\<Psi> P P' x A\<^sub>P \<Psi>\<^sub>P C.
                    \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<And>C. Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P; x \<sharp> \<Psi>;
                     x \<sharp> A\<^sub>P; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P';
                     A\<^sub>P \<sharp>* C; x \<sharp> C\<rbrakk> \<Longrightarrow>
                     Prop C \<Psi> (\<lparr>\<nu>x\<rparr>P) (\<lparr>\<nu>x\<rparr>P') (x#A\<^sub>P) \<Psi>\<^sub>P"
  and     rBang:    "\<And>\<Psi> P P' A\<^sub>P \<Psi>\<^sub>P C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<tau> \<prec> P'; guarded P; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>;  distinct A\<^sub>P;
                      \<And>C. Prop C \<Psi> (P \<parallel> !P) P' A\<^sub>P (\<Psi>\<^sub>P \<otimes> \<one>); \<Psi>\<^sub>P \<simeq> \<one>; supp \<Psi>\<^sub>P = ({}::name set);
                      A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P' ([]) (\<one>)"
  shows "Prop C \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P"
using Trans FrP \<open>distinct A\<^sub>P\<close>
proof(nominal_induct \<Psi> P Rs=="\<tau> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P avoiding: C arbitrary: P' rule: semanticsFrameInduct)
  case cAlpha
  thus ?case by(force intro: rAlpha simp add: residualInject)
next
  case cInput 
  thus ?case by(simp add: residualInject)
next
  case cOutput
  thus ?case by(simp add: residualInject)
next
  case cCase
  thus ?case by(force intro: rCase simp add: residualInject)
next
  case cPar1
  thus ?case by(force intro: rPar1 simp add: residualInject)
next
  case cPar2
  thus ?case by(force intro: rPar2 simp add: residualInject)
next
  case cComm1
  thus ?case by(force intro: rComm1 simp add: residualInject)
next
  case cComm2
  thus ?case by(force intro: rComm2 simp add: residualInject)
next
  case cOpen
  thus ?case by(simp add: residualInject)
next
  case cScope
  thus ?case by(force intro: rScope simp add: residualInject)
next
  case cBang
  thus ?case by(force intro: rBang simp add: residualInject)
qed

lemma inputFreshDerivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> N"

  shows "x \<sharp> P'"
proof -
  have "bn(M\<lparr>N\<rparr>) \<sharp>* subject(M\<lparr>N\<rparr>)" and "distinct(bn(M\<lparr>N\<rparr>))" by simp+
  with \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> show ?thesis using \<open>x \<sharp> P\<close> \<open>x \<sharp> N\<close>
  proof(nominal_induct \<Psi> P \<alpha>=="M\<lparr>N\<rparr>" P' avoiding: x rule: semanticsInduct)
    case(cAlpha \<Psi> P \<alpha> P' p x)
    thus ?case by simp
  next
    case(cInput \<Psi> M' K xvec N' Tvec P x)
    from \<open>K\<lparr>(N'[xvec::=Tvec])\<rparr> = M\<lparr>N\<rparr>\<close> have "M = K" and NeqN': "N = N'[xvec::=Tvec]" by(simp add: action.inject)+ 
    note \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> then
    moreover have "x \<sharp> Tvec" using \<open>set xvec \<subseteq> supp N'\<close> \<open>x \<sharp> N\<close> NeqN'
      by(blast intro: substTerm.subst3)
    moreover from \<open>xvec \<sharp>* x\<close> \<open>x \<sharp> M'\<lparr>\<lambda>*xvec N'\<rparr>.P\<close>
    have "x \<sharp> P" by(simp add: inputChainFresh) (simp add: name_list_supp fresh_def)
    ultimately show ?case using \<open>xvec \<sharp>* x\<close> by auto
  next
    case(cOutput \<Psi> M  K N P x)
    thus ?case by simp
  next
    case(cCase \<Psi> P P' \<phi> Cs x)
    thus ?case by(induct Cs, auto)
  next
    case(cPar1 \<Psi> \<Psi>\<^sub>Q P P' xvec Q x)
    thus ?case by simp
  next
    case(cPar2 \<Psi> \<Psi>\<^sub>P Q Q' xvec P x)
    thus ?case by simp
  next
    case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q x)
    thus ?case by simp
  next
    case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xwec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q x)
    thus ?case by simp
  next
    case(cOpen \<Psi> P M xvec yvec N P' x y)
    thus ?case by simp
  next
    case(cScope \<Psi> P P' x y)
    thus ?case by(simp add: abs_fresh)
  next
    case(cBang \<Psi> P P' x)
    thus ?case by simp
  qed
qed
  
lemma inputFreshChainDerivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* N"
  
  shows "xvec \<sharp>* P'"
using assms
by(induct xvec)
  (auto intro: inputFreshDerivative)

lemma outputFreshDerivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"
  and     "x \<sharp> P"
  and     "x \<sharp> xvec"

  shows "x \<sharp> N"
  and   "x \<sharp> P'"
proof -
  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  moreover from \<open>xvec \<sharp>* M\<close> have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from \<open>distinct xvec\<close> have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))" by simp
  ultimately show "x \<sharp> N" using \<open>x \<sharp> P\<close> \<open>x \<sharp> xvec\<close>
  proof(nominal_induct \<Psi> P \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: x arbitrary: M xvec N rule: semanticsInduct)
    case(cAlpha \<Psi> P \<alpha> P' p x M xvec N)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from \<open>(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by(simp add: fresh_star_bij)
    with \<open>distinctPerm p\<close> have "\<alpha>  = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>" by simp
    moreover from \<open>(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>x \<sharp> xvec\<close> have "x \<sharp> (bn(p \<bullet> \<alpha>))" by simp
    with \<open>(bn \<alpha>) \<sharp>* x\<close> \<open>x \<sharp> xvec\<close> S have "x \<sharp> (p \<bullet> xvec)"
      by(drule_tac pt_fresh_bij1[OF pt_name_inst, OF at_name_inst, where pi=p and x=xvec]) simp
    ultimately have "x \<sharp> (p \<bullet> N)" using \<open>x \<sharp> P\<close> by(rule_tac cAlpha)
    hence "(p \<bullet> x) \<sharp> (p \<bullet> p \<bullet> N)" by(simp add: pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> \<open>bn(\<alpha>) \<sharp>* x\<close> \<open>x \<sharp> (bn(p \<bullet> \<alpha>))\<close>S show ?case by simp
  next
    case cInput
    thus ?case by simp
  next
    case cOutput
    thus ?case by(simp add: action.inject)
  next
    case cCase
    thus ?case
      by(rule_tac cCase) (auto dest: memFresh)
  next
    case cPar1
    thus ?case by simp
  next
    case cPar2
    thus ?case by simp
  next
    case cComm1
    thus ?case by simp
  next
    case cComm2
    thus ?case by simp
  next
    case(cOpen \<Psi> P M xvec yvec N P' x y M' zvec N')
    from \<open>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> = M'\<lparr>\<nu>*zvec\<rparr>\<langle>N'\<rangle>\<close> have "zvec = xvec@x#yvec" and "N = N'"
      by(simp add: action.inject)+
    from \<open>y \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<sharp> y\<close>  have "y \<sharp> P" by(simp add: abs_fresh)
    moreover from \<open>y \<sharp> zvec\<close> \<open>zvec = xvec@x#yvec\<close>have "y \<sharp> (xvec@yvec)"
      by simp
    ultimately have "y \<sharp> N" by(rule_tac cOpen) auto
    with \<open>N = N'\<close> show ?case by simp
  next
    case cScope
    thus ?case by(auto simp add: abs_fresh)
  next
    case cBang
    thus ?case by simp
  qed
next
  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  moreover from \<open>xvec \<sharp>* M\<close> have "bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) \<sharp>* subject(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by simp
  moreover from \<open>distinct xvec\<close> have "distinct(bn(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>))" by simp
  ultimately show "x \<sharp> P'" using \<open>x \<sharp> P\<close> \<open>x \<sharp> xvec\<close>
  proof(nominal_induct \<Psi> P \<alpha>=="M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" P' avoiding: x arbitrary: M xvec N rule: semanticsInduct)
    case(cAlpha \<Psi> P \<alpha> P' p x M xvec N)
    have S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" by fact
    from \<open>(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> have "(p \<bullet> p \<bullet> \<alpha>) = p \<bullet> (M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>)" by(simp add: fresh_star_bij)
    with \<open>distinctPerm p\<close> have "\<alpha>  = (p \<bullet> M)\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle>" by simp
    moreover from \<open>(p \<bullet> \<alpha>) = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>x \<sharp> xvec\<close> have "x \<sharp> (bn(p \<bullet> \<alpha>))" by simp
    with \<open>(bn \<alpha>) \<sharp>* x\<close> \<open>x \<sharp> xvec\<close> S have "x \<sharp> (p \<bullet> xvec)"
      by(drule_tac pt_fresh_bij1[OF pt_name_inst, OF at_name_inst, where pi=p and x=xvec]) simp
    ultimately have "x \<sharp> P'" using \<open>x \<sharp> P\<close> by(rule_tac cAlpha)
    hence "(p \<bullet> x) \<sharp> (p \<bullet> P')" by(simp add: pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
    with \<open>distinctPerm p\<close> \<open>bn(\<alpha>) \<sharp>* x\<close> \<open>x \<sharp> (bn(p \<bullet> \<alpha>))\<close>S show ?case by simp
  next
    case cInput
    thus ?case by simp
  next
    case cOutput
    thus ?case by(simp add: action.inject)
  next
    case cCase
    thus ?case by(fastforce simp add: action.inject dest: memFresh)
  next
    case cPar1
    thus ?case by simp
  next
    case cPar2
    thus ?case by simp
  next
    case cComm1
    thus ?case by simp
  next
    case cComm2
    thus ?case by simp
  next
    case(cOpen \<Psi> P M xvec yvec N P' x y M' zvec N')
    from \<open>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> = M'\<lparr>\<nu>*zvec\<rparr>\<langle>N'\<rangle>\<close> have "zvec = xvec@x#yvec" 
      by(simp add: action.inject)
    from \<open>y \<sharp> \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<sharp> y\<close>  have "y \<sharp> P" by(simp add: abs_fresh)
    moreover from \<open>y \<sharp> zvec\<close> \<open>zvec = xvec@x#yvec\<close>have "y \<sharp> (xvec@yvec)"
      by simp
    ultimately show "y \<sharp> P'" by(rule_tac cOpen) auto
  next
    case cScope
    thus ?case by(auto simp add: abs_fresh)
  next
    case cBang
    thus ?case by simp
  qed
qed

lemma outputFreshChainDerivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"

  shows "yvec \<sharp>* N"
  and   "yvec \<sharp>* P'"
using assms
by(induct yvec) (auto intro: outputFreshDerivative)

lemma tauFreshDerivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
proof -
  have "bn(\<tau>) \<sharp>* subject(\<tau>)" and "distinct(bn(\<tau>))" by simp+
  with \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'\<close> show ?thesis using \<open>x \<sharp> P\<close>
  proof(nominal_induct \<Psi> P \<alpha>=="(\<tau>::('a action))" P' avoiding: x rule: semanticsInduct)
    case cAlpha
    thus ?case by simp
  next
    case cInput
    thus ?case by simp
  next
    case cOutput
    thus ?case by simp
  next 
    case cCase
    thus ?case by(auto dest: memFresh)
  next
    case cPar1
    thus ?case by simp
  next
    case cPar2
    thus ?case by simp
  next
    case cComm1
    thus ?case
      by(fastforce dest: inputFreshDerivative outputFreshDerivative simp add: resChainFresh)
  next
    case cComm2
    thus ?case
      by(fastforce dest: inputFreshDerivative outputFreshDerivative simp add: resChainFresh)
  next
    case cOpen
    thus ?case by simp
  next
    case cScope
    thus ?case by(simp add: abs_fresh)
  next
    case cBang
    thus ?case by simp
  qed
qed

lemma tauFreshChainDerivative:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     "xvec \<sharp>* P"
  
  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tauFreshDerivative)

lemma freeFreshDerivative:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P"

  shows   "x \<sharp> P'"
using assms
by(rule_tac actionCases[where \<alpha>=\<alpha>])
  (auto intro: inputFreshDerivative tauFreshDerivative outputFreshDerivative)

lemma freeFreshChainDerivative:
  fixes \<Psi>     :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   \<alpha>     :: "'a action"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* \<alpha>"

  shows   "xvec \<sharp>* P'"
using assms
by(auto intro: freeFreshDerivative simp add: fresh_star_def)

lemma Input:
  fixes \<Psi>    :: 'b
  and   M    :: 'a
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Tvec :: "'a list"

  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     "distinct xvec"
  and     "set xvec \<subseteq> supp N"
  and     "length xvec = length Tvec"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>N[xvec::=Tvec]\<rparr> \<prec> P[xvec::=Tvec]"
proof -
  obtain p where xvecFreshPsi: "((p::name prm) \<bullet> (xvec::name list)) \<sharp>* \<Psi>"
             and xvecFreshM: "(p \<bullet> xvec) \<sharp>* M"
             and xvecFreshN: "(p \<bullet> xvec) \<sharp>* N"
             and xvecFreshK: "(p \<bullet> xvec) \<sharp>* K"
             and xvecFreshTvec: "(p \<bullet> xvec) \<sharp>* Tvec"
             and xvecFreshP: "(p \<bullet> xvec) \<sharp>* P"
             and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
             and dp: "distinctPerm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, K, N, P, Tvec)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)  
  note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close>
  moreover from \<open>distinct xvec\<close> have "distinct(p \<bullet> xvec)"
    by simp
  moreover from \<open>(set xvec) \<subseteq> (supp N)\<close> have "(p \<bullet> (set xvec)) \<subseteq> (p \<bullet> (supp N))"
    by simp
  hence "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
    by(simp add: eqvts)
  moreover from \<open>length xvec = length Tvec\<close> have "length(p \<bullet> xvec) = length Tvec"
    by simp
  ultimately have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr> \<prec> (p \<bullet> P)[(p \<bullet> xvec)::=Tvec]"
    using xvecFreshPsi xvecFreshM xvecFreshK xvecFreshTvec
    by(rule_tac cInput)
  thus ?thesis using xvecFreshN xvecFreshP S \<open>length xvec = length Tvec\<close> dp
    by(auto simp add: inputChainAlpha' substTerm.renaming renaming)
qed

lemma residualAlpha:
  fixes p :: "name prm"
  and   \<alpha> :: "'a action"
  and   P :: "('a, 'b, 'c) psi"

  assumes "bn(p \<bullet> \<alpha>) \<sharp>* object  \<alpha>"
  and     "bn(p \<bullet> \<alpha>) \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "bn(p \<bullet> \<alpha>) \<sharp>* subject \<alpha>"
  and     "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"

  shows "\<alpha> \<prec> P = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P)"
using assms
apply(rule_tac \<alpha>=\<alpha> in actionCases)
apply(simp only: eqvts bn.simps)
apply simp
apply(simp add: boundOutputChainAlpha'' residualInject)
by simp

lemma Par1:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "bn \<alpha> \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* \<alpha>"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q   :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
    and Q    :: "('a, 'b, 'c) psi"

    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
    and     "bn \<alpha> \<sharp>* Q"
    and     "bn \<alpha> \<sharp>* subject \<alpha>"
    and     "A\<^sub>Q \<sharp>* \<Psi>"
    and     "A\<^sub>Q \<sharp>* P"
    and     "A\<^sub>Q \<sharp>* \<alpha>"
    and     "distinct A\<^sub>Q"
  
    have  "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)"
    proof -
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "distinct(bn \<alpha>)" by(rule boundOutputDistinct)
      obtain q::"name prm" where "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(q \<bullet> \<alpha>) \<sharp>* P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q" and "bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>"
                             and "bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>Q" and "bn(q \<bullet> \<alpha>) \<sharp>* P'" and "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>\<^sub>Q"
                             and Sq: "(set q) \<subseteq> (set (bn \<alpha>)) \<times> (set(bn(q \<bullet> \<alpha>)))"
        by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>Q, \<Psi>\<^sub>Q, P')" in name_list_avoiding) (auto simp add: eqvts)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>Q) \<sharp>* P" and "(p \<bullet> A\<^sub>Q) \<sharp>* Q" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<alpha>" 
                              and "(p \<bullet> A\<^sub>Q) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>Q) \<sharp>* P'" 
                             and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q" and Sp: "(set p) \<subseteq> (set A\<^sub>Q) \<times> (set(p \<bullet> A\<^sub>Q))"
        by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, \<alpha>, bn \<alpha>, q \<bullet> \<alpha>, P', (q \<bullet> P'), \<Psi>\<^sub>Q)" in name_list_avoiding) auto
      from \<open>distinct(bn \<alpha>)\<close> have "distinct(bn(q \<bullet> \<alpha>))" 
        by(rule_tac \<alpha>=\<alpha> in actionCases) (auto simp add: eqvts)
      from \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>Q\<close> Sq have "A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)"
        apply(rule_tac \<alpha>=\<alpha> in actionCases)
        apply(simp only: bn.simps eqvts, simp)
        apply(simp add: freshChainSimps)
        by simp
      from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "(q \<bullet> (bn \<alpha>)) \<sharp>* (q \<bullet> (subject \<alpha>))"
        by(simp add: fresh_star_bij)
      hence "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)" by(simp add: eqvts)
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* P'\<close> \<open>bn \<alpha> \<sharp>* (subject \<alpha>)\<close> Sq
      have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> P')"
        by(force simp add: residualAlpha)
      hence "A\<^sub>Q \<sharp>* (q \<bullet> P')" using  \<open>bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)\<close>
        by(auto intro: freeFreshChainDerivative)
      from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> (p \<bullet> P) \<longmapsto>p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> P'))"
        by(rule semantics.eqvt)
      with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> P')\<close>
           \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')\<close> Sp
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> P')" by(simp add: eqvts)
      moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close> Sp have  "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), (p \<bullet> \<Psi>\<^sub>Q)\<rangle>"
        by(simp add: frameChainAlpha' eqvts)
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close> Sp 
      have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)"
        by(simp add: freshAlphaPerm)
      moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>Q)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> ((q \<bullet> P') \<parallel> Q)"
        using \<open>(p \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close>
              \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P\<close> 
              \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* (subject (q \<bullet> \<alpha>))\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close>
        by(rule_tac cPar1)
        
      thus ?thesis using \<open>bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* Q\<close> Sq
        by(force simp add: residualAlpha) 
    qed
  }
  note Goal = this
  from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
  obtain A\<^sub>Q' where FrQ: "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* \<alpha>"
    by(rule_tac C="(\<Psi>, P, \<alpha>)" in distinctFrame) auto
  show ?thesis
  proof(induct rule: actionCases[where \<alpha>=\<alpha>])
    case(cInput M N)
    from Trans FrQ \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close> \<open>distinct A\<^sub>Q'\<close> \<open>bn \<alpha> \<sharp>* Q\<close>
    show ?case using \<open>\<alpha> = M\<lparr>N\<rparr>\<close> by(force intro: Goal)
  next
    case cTau 
    from Trans FrQ \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close> \<open>distinct A\<^sub>Q'\<close> \<open>bn \<alpha> \<sharp>* Q\<close>
    show ?case using \<open>\<alpha> = \<tau>\<close> by(force intro: Goal)
  next
    case(cOutput M xvec N)
    from \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> have "xvec \<sharp>* A\<^sub>Q'" and "xvec \<sharp>* Q"
      by simp+
    obtain p where "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* Q"
               and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q'" 
               and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
      by(rule_tac xvec=xvec and c="(N, P', Q, M, A\<^sub>Q')" in name_list_avoiding) auto
    from Trans \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
    with \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> S
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
      by(simp add: boundOutputChainAlpha'' create_residual.simps)
    moreover from \<open>xvec \<sharp>* A\<^sub>Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close> S
    have "A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>)" by(simp add: freshChainSimps del: actionFreshChain)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P') \<parallel> Q"
      using FrQ \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>distinct A\<^sub>Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>\<close>
           \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
      by(force intro: Goal)
    with \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> S \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
    show ?case
      by(simp add: boundOutputChainAlpha'' eqvts create_residual.simps)
  qed
qed

lemma Par2:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>P   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "bn \<alpha> \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>P   :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and \<alpha>    :: "'a action"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and P    :: "('a, 'b, 'c) psi"

    assume "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
    and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
    and     "bn \<alpha> \<sharp>* P"
    and     "bn \<alpha> \<sharp>* subject \<alpha>"
    and     "A\<^sub>P \<sharp>* \<Psi>"
    and     "A\<^sub>P \<sharp>* Q"
    and     "A\<^sub>P \<sharp>* \<alpha>"
    and     "distinct A\<^sub>P"
  
    have  "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
    proof -
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> have "distinct(bn \<alpha>)" by(rule boundOutputDistinct)
      obtain q::"name prm" where "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(q \<bullet> \<alpha>) \<sharp>* P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q" and "bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>"
                             and "bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>P" and "bn(q \<bullet> \<alpha>) \<sharp>* Q'" and "bn(q \<bullet> \<alpha>) \<sharp>* \<Psi>\<^sub>P"
                             and Sq: "(set q) \<subseteq> (set (bn \<alpha>)) \<times> (set(bn(q \<bullet> \<alpha>)))"
        by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>P, \<Psi>\<^sub>P, Q')" in name_list_avoiding) (auto simp add: eqvts)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>" 
                              and "(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>P) \<sharp>* Q'" 
                              and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" 
                              and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
        by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, \<alpha>, q \<bullet> \<alpha>, Q', (q \<bullet> Q'), \<Psi>\<^sub>P)" in name_list_avoiding) auto
      from \<open>distinct(bn \<alpha>)\<close> have "distinct(bn(q \<bullet> \<alpha>))" 
        by(rule_tac \<alpha>=\<alpha> in actionCases) (auto simp add: eqvts)
      from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>P\<close> Sq have "A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)"
        apply(rule_tac \<alpha>=\<alpha> in actionCases)
        apply(simp only: bn.simps eqvts, simp)
        apply(simp add: freshChainSimps)
        by simp
      from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "(q \<bullet> (bn \<alpha>)) \<sharp>* (q \<bullet> (subject \<alpha>))"
        by(simp add: fresh_star_bij)
      hence "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)" by(simp add: eqvts)
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* Q'\<close> \<open>bn \<alpha> \<sharp>* (subject \<alpha>)\<close> Sq
      have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')"
        by(force simp add: residualAlpha)
      hence "A\<^sub>P \<sharp>* (q \<bullet> Q')" using  \<open>bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)\<close>
        by(auto intro: freeFreshChainDerivative)
      from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> (p \<bullet> Q) \<longmapsto>p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> Q'))"
        by(rule semantics.eqvt)
      with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> Q')\<close>
           \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')\<close> Sp
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')" by(simp add: eqvts)
      moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close> Sp have  "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
        by(simp add: frameChainAlpha' eqvts)
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close> Sp 
      have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
        by(simp add: freshAlphaPerm)
      moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)" by simp
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> (P \<parallel> (q \<bullet> Q'))"
        using \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close>
              \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P\<close> 
              \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* (subject (q \<bullet> \<alpha>))\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close>
        by(rule_tac cPar2)
        
      thus ?thesis using \<open>bn(q \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* Q'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* P\<close> Sq
        by(force simp add: residualAlpha) 
    qed
  }
  note Goal = this
  from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
  obtain A\<^sub>P' where FrP: "extractFrame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* \<alpha>"
    by(rule_tac C="(\<Psi>, Q, \<alpha>)" in distinctFrame) auto
  show ?thesis
  proof(induct rule: actionCases[where \<alpha>=\<alpha>])
    case(cInput M N)
    from Trans FrP \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>\<close> \<open>distinct A\<^sub>P'\<close> \<open>bn \<alpha> \<sharp>* P\<close>
    show ?case using \<open>\<alpha> = M\<lparr>N\<rparr>\<close> by(force intro: Goal)
  next
    case cTau 
    from Trans FrP \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>\<close> \<open>distinct A\<^sub>P'\<close> \<open>bn \<alpha> \<sharp>* P\<close>
    show ?case using \<open>\<alpha> = \<tau>\<close> by(force intro: Goal)
  next
    case(cOutput M xvec N)
    from \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* P\<close> have "xvec \<sharp>* A\<^sub>P'" and "xvec \<sharp>* P"
      by simp+
    obtain p where "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* P"
               and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" 
               and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
      by(rule_tac xvec=xvec and c="(N, Q', P, M, A\<^sub>P')" in name_list_avoiding) auto
    from Trans \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by simp
    with \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> S
    have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> Q')"
      by(simp add: boundOutputChainAlpha'' create_residual.simps)
    moreover from \<open>xvec \<sharp>* A\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>\<close> S
    have "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" by(simp add: freshChainSimps del: actionFreshChain)
    ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P \<parallel> (p \<bullet> Q')"
      using FrP \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>distinct A\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>\<close>
           \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
      by(force intro: Goal)
    with \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> S \<open>\<alpha> = M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close>
    show ?case
      by(simp add: boundOutputChainAlpha'' eqvts create_residual.simps)
  qed
qed

lemma Open:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<in> supp N"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from Trans have "distinct(xvec@yvec)" by(force dest: boundOutputDistinct)
  hence "xvec \<sharp>* yvec" by(induct xvec) auto
  
  obtain p where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P"  and "(p \<bullet> yvec) \<sharp>* M"
             and "(p \<bullet> yvec) \<sharp>* yvec" and "(p \<bullet> yvec) \<sharp>* N" and "(p \<bullet> yvec) \<sharp>* P'"
             and "x \<sharp> (p \<bullet> yvec)" and "(p \<bullet> yvec) \<sharp>* xvec"
             and Sp: "(set p) \<subseteq> (set yvec) \<times> (set(p \<bullet> yvec))"
    by(rule_tac xvec=yvec and c="(\<Psi>, P, M, xvec, yvec, N, P', x)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)
  obtain q where "(q \<bullet> xvec) \<sharp>* \<Psi>" and "(q \<bullet> xvec) \<sharp>* P"  and "(q \<bullet> xvec) \<sharp>* M"
             and "(q \<bullet> xvec) \<sharp>* xvec" and "(q \<bullet> xvec) \<sharp>* N" and "(q \<bullet> xvec) \<sharp>* P'"
             and "x \<sharp> (q \<bullet> xvec)" and "(q \<bullet> xvec) \<sharp>* yvec"
             and "(q \<bullet> xvec) \<sharp>* p" and "(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)"
             and Sq: "(set q) \<subseteq> (set xvec) \<times> (set(q \<bullet> xvec))"
    by(rule_tac xvec=xvec and c="(\<Psi>, P, M, xvec, yvec, p \<bullet> yvec, N, P', x, p)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

  note \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  moreover from \<open>(p \<bullet> yvec) \<sharp>* N\<close> \<open>(q \<bullet> xvec) \<sharp>* N\<close> \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> Sp Sq 
  have "((p@q) \<bullet> (xvec @ yvec)) \<sharp>* N" apply(simp only: eqvts) apply(simp only: pt2[OF pt_name_inst])
    by simp
  moreover from \<open>(p \<bullet> yvec) \<sharp>* P'\<close> \<open>(q \<bullet> xvec) \<sharp>* P'\<close> \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> Sp Sq 
  have "((p@q) \<bullet> (xvec @ yvec)) \<sharp>* P'" by(simp del: freshAlphaPerm add: eqvts pt2[OF pt_name_inst])
  moreover from Sp Sq \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close>
  have Spq: "set(p@q) \<subseteq> set(xvec@yvec) \<times> set((p@q) \<bullet> (xvec@yvec))"
    by(simp add: pt2[OF pt_name_inst] eqvts) blast
  ultimately have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*((p@q) \<bullet> (xvec@yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    apply(simp add: create_residual.simps)
    by(erule_tac rev_mp) (subst boundOutputChainAlpha, auto)

  with  Sp Sq \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close>
  have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*((q \<bullet> xvec)@(p \<bullet> yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(simp add: eqvts pt2[OF pt_name_inst] del: freshAlphaPerm)
  moreover from \<open>x \<in> supp N\<close> have "((p@q) \<bullet> x) \<in> (p@q) \<bullet> (supp N)"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> Sp Sq
  have "x \<in> supp((p@q)\<bullet> N)" by(simp add: eqvts pt2[OF pt_name_inst])
  moreover from \<open>distinct(xvec@yvec)\<close> have "distinct(q \<bullet> xvec)" and "distinct(p \<bullet> yvec)"
    by auto
  moreover note \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> \<Psi>\<close> 
                \<open>(q \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* M\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close>
                \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close> \<open>(p \<bullet> yvec) \<sharp>* M\<close> \<open>distinct(q \<bullet> xvec)\<close>
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*((q \<bullet> xvec)@x#(p \<bullet> yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(rule_tac cOpen) 
  with \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close>
       \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> Sp Sq
  have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*((p@q) \<bullet> (xvec@x#yvec))\<rparr>\<langle>((p@q) \<bullet> N)\<rangle> \<prec> ((p@q) \<bullet> P')"
    by(simp add: eqvts pt2[OF pt_name_inst] del: freshAlphaPerm)
  thus ?thesis using \<open>((p@q) \<bullet> (xvec @ yvec)) \<sharp>* N\<close> \<open>((p@q) \<bullet> (xvec @ yvec)) \<sharp>* P'\<close> Spq
    apply(simp add: create_residual.simps)
    by(erule_tac rev_mp) (subst boundOutputChainAlpha, auto)
qed

lemma Scope:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  {
    fix \<Psi> P M xvec N P' x

    assume "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    and    "(x::name) \<sharp> \<Psi>"
    and    "x \<sharp> M"
    and    "x \<sharp> xvec"
    and    "x \<sharp> N"

    obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* xvec" 
                           and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P'" and "x \<sharp> (p \<bullet> xvec)"
                           and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))"
      by(rule_tac xvec=xvec and c="(\<Psi>, P, M, xvec, N, P', x)" in name_list_avoiding)
        (auto simp add: eqvts fresh_star_prod)
    from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> S
    have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
      by(simp add: boundOutputChainAlpha'' create_residual.simps)
    moreover hence "distinct(p \<bullet> xvec)" by(force dest: boundOutputDistinct)
    moreover note \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close>
    moreover from \<open>x \<sharp> xvec\<close> \<open>x \<sharp> p \<bullet> xvec\<close> \<open>x \<sharp> N\<close> S have "x \<sharp> (p \<bullet> N)"
      by(simp add: fresh_left del: freshAlphaSwap)
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P')" using \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close>
      by(rule_tac cScope) auto
    moreover from \<open>x \<sharp> xvec\<close> \<open>x \<sharp> p \<bullet> xvec\<close> S have "p \<bullet> x = x" by simp
    ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> (\<lparr>\<nu>x\<rparr>P'))" by simp
    moreover from \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> (p \<bullet> xvec)\<close> have "(p \<bullet> xvec) \<sharp>* \<lparr>\<nu>x\<rparr>P'" 
      by(simp add: abs_fresh_star)
    ultimately have"\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> \<lparr>\<nu>x\<rparr>P'" using \<open>(p \<bullet> xvec) \<sharp>* N\<close> S
      by(simp add: boundOutputChainAlpha'' create_residual.simps)
  }
  note Goal = this
  show ?thesis
  proof(induct rule: actionCases[where \<alpha>=\<alpha>])
    case(cInput M N)
    with assms show ?case by(force intro: cScope)
  next
    case(cOutput M xvec N)
    with assms show ?case by(force intro: Goal)
  next
    case cTau
    with assms show ?case by(force intro: cScope)
  qed
qed

lemma inputSwapFrameSubject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
using assms
proof(nominal_induct avoiding: x y rule: inputInduct)
  case(cInput \<Psi> M K xvec N Tvec P x y)
  from \<open>x \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.P\<close> have "x \<sharp> M" by simp
  from \<open>y \<sharp> M\<lparr>\<lambda>*xvec N\<rparr>.P\<close> have "y \<sharp> M" by simp
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> M) \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(rule chanEqClosed)
  with \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close>  have "([(x, y)] \<bullet> \<Psi>) \<turnstile> M \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(simp)
  thus ?case using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
    by(rule Input)
next
  case(cCase \<Psi> P M N P' \<phi> Cs x y)
  from \<open>x \<sharp> Cases Cs\<close> \<open>y \<sharp> Cases Cs\<close> \<open>(\<phi>, P) mem Cs\<close> have "x \<sharp> \<phi>" and "x \<sharp> P" and "y \<sharp> \<phi>" and "y \<sharp> P"
    by(auto dest: memFresh)
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "([(x ,y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by(rule cCase)
  moreover note \<open>(\<phi>, P) mem Cs\<close>
  moreover from \<open>\<Psi> \<turnstile> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> \<phi>)" by(rule statClosed)
  with \<open>x \<sharp> \<phi>\<close> \<open>y \<sharp> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> \<phi>" by simp
  ultimately show ?case using \<open>guarded P\<close> by(rule Case)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q x y)
  from \<open>x \<sharp> P \<parallel> Q\<close> have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from \<open>y \<sharp> P \<parallel> Q\<close> have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(simp add: eqvts)

  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "([(x, y)] \<bullet> (extractFrame Q)) = ([(x, y)] \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>)"
    by simp
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>x \<sharp> Q\<close> \<open>A\<^sub>Q \<sharp>* y\<close> \<open>y \<sharp> Q\<close> have "\<langle>A\<^sub>Q, ([(x, y)] \<bullet> \<Psi>\<^sub>Q)\<rangle> = extractFrame Q"
    by(simp add: eqvts)
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>A\<^sub>Q \<sharp>* y\<close> have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from \<open>A\<^sub>Q \<sharp>* M\<close> have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>A\<^sub>Q \<sharp>* y\<close> have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P x y)
  from \<open>x \<sharp> P \<parallel> Q\<close> have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from \<open>y \<sharp> P \<parallel> Q\<close> have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> Q; y \<sharp> Q\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> Q'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(simp add: eqvts)

  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> have "([(x, y)] \<bullet> (extractFrame P)) = ([(x, y)] \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>)"
    by simp
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>y \<sharp> P\<close> have "\<langle>A\<^sub>P, ([(x, y)] \<bullet> \<Psi>\<^sub>P)\<rangle> = extractFrame P"
    by(simp add: eqvts)
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from \<open>A\<^sub>P \<sharp>* M\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* N\<close>
    by(rule_tac Par2) auto
next
  case(cScope \<Psi> P M N P' z x y)
  from \<open>x \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> x\<close> have "x \<sharp> P" by(simp add: abs_fresh)
  from \<open>y \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> y\<close> have "y \<sharp> P" by(simp add: abs_fresh)
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by simp
  moreover with \<open>z \<sharp> \<Psi>\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with \<open>z \<sharp> M\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using \<open>z \<sharp> N\<close>
    by(rule_tac Scope) (assumption | simp)+
next
  case(cBang \<Psi> P M N P' x y)
  thus ?case by(force intro: Bang)
qed

lemma inputPermFrameSubject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
using S
proof(induct p)
  case Nil
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
  show ?case by simp
next
  case(Cons a p)
  from \<open>set(a#p) \<subseteq> Xs \<times> Ys\<close> have "set p \<subseteq> Xs \<times> Ys" by auto
  with \<open>set p \<subseteq> Xs \<times> Ys \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'\<close>
  have Trans: "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by simp
  from \<open>set(a#p) \<subseteq> Xs \<times> Ys\<close> show ?case
  proof(cases a, clarsimp)
    fix a b
    assume "a \<in> Xs" and "b \<in> Ys"
    with \<open>Xs \<sharp>* P\<close> \<open>Ys \<sharp>* P\<close>
    have "a \<sharp> P" and "b \<sharp> P"
      by(auto simp add: fresh_star_def)
    with Trans show "([(a, b)] \<bullet> p \<bullet> \<Psi>) \<rhd> P \<longmapsto> ([(a, b)] \<bullet> p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
      by(rule inputSwapFrameSubject)
  qed  
qed

lemma inputSwapSubject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto> ([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule inputSwapFrameSubject)
  with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> show ?thesis
    by simp
qed

lemma inputPermSubject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"
  and     "Xs \<sharp>* \<Psi>"
  and     "Ys \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> S \<open>Xs \<sharp>* P\<close> \<open>Ys \<sharp>* P\<close>
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule inputPermFrameSubject)
  with \<open>Xs \<sharp>* \<Psi>\<close> \<open>Ys \<sharp>* \<Psi>\<close> S show ?thesis
    by simp
qed

lemma inputSwapFrame:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name
  and   y  :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> M"
  and     "y \<sharp> M"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto> M\<lparr>N\<rparr> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule inputSwapFrameSubject)
  with \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> show ?thesis
    by simp
qed

lemma inputPermFrame:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> Xs \<times> Ys"
  and     "Xs \<sharp>* P"
  and     "Ys \<sharp>* P"
  and     "Xs \<sharp>* M"
  and     "Ys \<sharp>* M"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto> M\<lparr>N\<rparr> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> S \<open>Xs \<sharp>* P\<close> \<open>Ys \<sharp>* P\<close>
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule inputPermFrameSubject)
  with \<open>Xs \<sharp>* M\<close> \<open>Ys \<sharp>* M\<close> S show ?thesis
    by simp
qed

lemma inputAlpha:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))"
  and     "distinctPerm p"
  and     "xvec \<sharp>* P"
  and     "(p \<bullet> xvec) \<sharp>* P"

  shows "\<Psi> \<rhd> P \<longmapsto>M\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> P')"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
  have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" by(rule_tac inputPermFrameSubject) auto
  hence "(p \<bullet> p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<longmapsto>(p \<bullet> ((p \<bullet> M)\<lparr>N\<rparr> \<prec> P'))" by(rule eqvts)
  with \<open>distinctPerm p\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>set p \<subseteq> (set xvec) \<times> (set (p \<bullet> xvec))\<close> 
  show ?thesis by(simp add: eqvts)
qed

lemma frameFresh[dest]:
  fixes x  :: name
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "x \<sharp> A\<^sub>F"
  and     "x \<sharp> \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"

  shows "x \<sharp> \<Psi>\<^sub>F"
using assms
by(simp add: frameResChainFresh) (simp add: fresh_def name_list_supp)

lemma outputSwapFrameSubject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
proof(nominal_induct avoiding: x y rule: outputInduct')
  case cAlpha
  thus ?case by(simp add: create_residual.simps boundOutputChainAlpha'')
next
  case(cOutput \<Psi> M K N P x y)
  from \<open>x \<sharp> M\<langle>N\<rangle>.P\<close> have "x \<sharp> M" by simp
  from \<open>y \<sharp> M\<langle>N\<rangle>.P\<close> have "y \<sharp> M" by simp
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> M) \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(rule chanEqClosed)
  with \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close>  have "([(x, y)] \<bullet> \<Psi>) \<turnstile> M \<leftrightarrow> ([(x, y)] \<bullet> K)"
    by(simp)
  thus ?case by(rule Output)
next
  case(cCase \<Psi> P M xvec N P' \<phi> Cs x y)
  from \<open>x \<sharp> Cases Cs\<close> \<open>y \<sharp> Cases Cs\<close> \<open>(\<phi>, P) mem Cs\<close> have "x \<sharp> \<phi>" and "x \<sharp> P" and "y \<sharp> \<phi>" and "y \<sharp> P"
    by(auto dest: memFresh)
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> have "([(x ,y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule cCase)
  moreover note \<open>(\<phi>, P) mem Cs\<close>
  moreover from \<open>\<Psi> \<turnstile> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> ([(x, y)] \<bullet> \<phi>)" by(rule statClosed)
  with \<open>x \<sharp> \<phi>\<close> \<open>y \<sharp> \<phi>\<close> have "([(x, y)] \<bullet> \<Psi>) \<turnstile> \<phi>" by simp
  ultimately show ?case using \<open>guarded P\<close> by(rule Case)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q x y)
  from \<open>x \<sharp> P \<parallel> Q\<close> have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from \<open>y \<sharp> P \<parallel> Q\<close> have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(simp add: eqvts)

  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "([(x, y)] \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>) = ([(x, y)] \<bullet> (extractFrame Q))"
    by simp
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>x \<sharp> Q\<close> \<open>A\<^sub>Q \<sharp>* y\<close> \<open>y \<sharp> Q\<close> have "\<langle>A\<^sub>Q, ([(x, y)] \<bullet> \<Psi>\<^sub>Q)\<rangle> = extractFrame Q"
    by(simp add: eqvts)
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>A\<^sub>Q \<sharp>* y\<close> have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from \<open>A\<^sub>Q \<sharp>* M\<close> have "([(x, y)] \<bullet> A\<^sub>Q) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>Q \<sharp>* x\<close> \<open>A\<^sub>Q \<sharp>* y\<close> have "A\<^sub>Q \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* N\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close>
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q M xvec N Q' A\<^sub>P P x y)
  from \<open>x \<sharp> P \<parallel> Q\<close> have "x \<sharp> P" and "x \<sharp> Q" by simp+
  from \<open>y \<sharp> P \<parallel> Q\<close> have "y \<sharp> P" and "y \<sharp> Q" by simp+
  from \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> Q; y \<sharp> Q\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<otimes> ([(x, y)] \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(simp add: eqvts)

  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> have "([(x, y)] \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>) = ([(x, y)] \<bullet> (extractFrame P))"
    by simp
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>x \<sharp> P\<close> \<open>A\<^sub>P \<sharp>* y\<close> \<open>y \<sharp> P\<close> have "\<langle>A\<^sub>P, ([(x, y)] \<bullet> \<Psi>\<^sub>P)\<rangle> = extractFrame P"
    by(simp add: eqvts)
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> \<Psi>)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> \<Psi>)" by simp
  moreover from \<open>A\<^sub>P \<sharp>* M\<close> have "([(x, y)] \<bullet> A\<^sub>P) \<sharp>* ([(x, y)] \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>P \<sharp>* x\<close> \<open>A\<^sub>P \<sharp>* y\<close> have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> M)" by simp
  ultimately show ?case using \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
    by(rule_tac Par2) auto
next
  case(cOpen \<Psi> P M xvec yvec N P' z x y)
  from \<open>x \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> x\<close> have "x \<sharp> P" by(simp add: abs_fresh)
  from \<open>y \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> y\<close> have "y \<sharp> P" by(simp add: abs_fresh)
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
  moreover with \<open>z \<sharp> \<Psi>\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with \<open>z \<sharp> M\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using \<open>z \<in> supp N\<close> \<open>z \<sharp> xvec\<close> \<open>z \<sharp> yvec\<close>
    by(rule_tac Open) (assumption | simp)+
next
  case(cScope \<Psi> P M xvec N P' z x y)
  from \<open>x \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> x\<close> have "x \<sharp> P" by(simp add: abs_fresh)
  from \<open>y \<sharp> \<lparr>\<nu>z\<rparr>P\<close> \<open>z \<sharp> y\<close> have "y \<sharp> P" by(simp add: abs_fresh)
  from \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>\<And>x y. \<lbrakk>x \<sharp> P; y \<sharp> P\<rbrakk> \<Longrightarrow> ([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
  moreover with \<open>z \<sharp> \<Psi>\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> \<Psi>"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> \<Psi>" by simp
  moreover with \<open>z \<sharp> M\<close> have "([(x, y)] \<bullet> z) \<sharp> [(x, y)] \<bullet> M"
    by(simp add: pt_fresh_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>z \<sharp> x\<close> \<open>z \<sharp> y\<close> have "z \<sharp> [(x, y)] \<bullet> M" by simp
  ultimately show ?case using \<open>z \<sharp> N\<close> \<open>z \<sharp> xvec\<close>
    by(rule_tac Scope) (assumption | simp)+
next
  case(cBang \<Psi> P M B x y)
  thus ?case by(force intro: Bang)
qed

lemma outputPermFrameSubject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  {
    fix xvec N P' Xs YS
    assume "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and "xvec \<sharp>* M" and "xvec \<sharp>* yvec" and "xvec \<sharp>* zvec"
    have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using S
    proof(induct p)
      case Nil
      from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
      show ?case by simp
    next
      case(Cons a p)
      from \<open>set(a#p) \<subseteq> set yvec \<times> set zvec\<close> have "set p \<subseteq> set yvec \<times> set zvec" by auto
      then have Trans: "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule Cons)
      from \<open>set(a#p) \<subseteq> set yvec \<times> set zvec\<close> show ?case
      proof(cases a, clarsimp)
        fix x y
        note Trans
        moreover from \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* zvec\<close> \<open>set p \<subseteq> set yvec \<times> set zvec\<close> \<open>xvec \<sharp>* M\<close> have "xvec \<sharp>* (p \<bullet> M)"
          by(simp add: freshChainSimps)
        moreover assume "x \<in> set yvec" and "y \<in> set zvec"
        with \<open>yvec \<sharp>* P\<close> \<open>zvec \<sharp>* P\<close> have "x \<sharp> P" and "y \<sharp> P"
          by(auto simp add: fresh_star_def)
        ultimately show "([(x, y)] \<bullet> p \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule outputSwapFrameSubject)
      qed
    qed
  }
  note Goal = this
  obtain q::"name prm" where "(q \<bullet> xvec) \<sharp>* yvec" and "(q \<bullet> xvec) \<sharp>* zvec" and "(q \<bullet> xvec) \<sharp>* xvec" 
                         and "(q \<bullet> xvec) \<sharp>* N" and "(q \<bullet> xvec) \<sharp>* P'" and "(q \<bullet> xvec) \<sharp>* M" 
                         and Sq: "(set q) \<subseteq> (set xvec) \<times> (set(q \<bullet> xvec))"
    by(rule_tac xvec=xvec and c="(P, xvec, yvec, zvec, N, M, P')" in name_list_avoiding) auto
  with \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(q \<bullet> xvec)\<rparr>\<langle>(q \<bullet> N)\<rangle> \<prec> (q \<bullet> P')"
    by(simp add: boundOutputChainAlpha'' residualInject)
  hence "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*(q \<bullet> xvec)\<rparr>\<langle>(q \<bullet> N)\<rangle> \<prec> (q \<bullet> P')"
    using \<open>(q \<bullet> xvec) \<sharp>* M\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* zvec\<close>
    by(rule Goal)
  with \<open>(q \<bullet> xvec) \<sharp>* N\<close> \<open>(q \<bullet> xvec) \<sharp>* P'\<close> Sq show ?thesis
    by(simp add: boundOutputChainAlpha'' residualInject)
qed   

lemma outputSwapSubject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule outputSwapFrameSubject)
  with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> show ?thesis
    by simp
qed

lemma outputPermSubject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from assms have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
   by(rule_tac outputPermFrameSubject)
  with S \<open>yvec \<sharp>* \<Psi>\<close> \<open>zvec \<sharp>* \<Psi>\<close> show ?thesis
    by simp
qed
 
lemma outputSwapFrame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   x    :: name
  and   y    :: name

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "xvec \<sharp>* M"
  and     "x \<sharp> P"
  and     "y \<sharp> P"
  and     "x \<sharp> M"
  and     "y \<sharp> M"

  shows "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>xvec \<sharp>* M\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close>
  have "([(x, y)] \<bullet> \<Psi>) \<rhd> P \<longmapsto>([(x, y)] \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule outputSwapFrameSubject)
  with \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> show ?thesis
    by simp
qed

lemma outputPermFrame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   B    :: "('a, 'b, 'c) boundOutput"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"
  and     "yvec \<sharp>* M"
  and     "zvec \<sharp>* M"

  shows "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from assms have "(p \<bullet> \<Psi>) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac outputPermFrameSubject)
  with S \<open>yvec \<sharp>* M\<close> \<open>zvec \<sharp>* M\<close> show ?thesis
    by simp
qed

lemma Comm1:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   xvec :: "name list"
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  
  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* K"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and xvec :: "name list"
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    and    "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
    and    "distinct A\<^sub>P"
    and    "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    and    "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
    and    "distinct A\<^sub>Q"
    and    "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    and    "A\<^sub>P \<sharp>* \<Psi>"
    and    "A\<^sub>P \<sharp>* P"
    and    "A\<^sub>P \<sharp>* Q"
    and    "A\<^sub>P \<sharp>* M"
    and    "A\<^sub>P \<sharp>* A\<^sub>Q"
    and    "A\<^sub>Q \<sharp>* \<Psi>"
    and    "A\<^sub>Q \<sharp>* P"
    and    "A\<^sub>Q \<sharp>* Q"
    and    "A\<^sub>Q \<sharp>* K"
    and    "xvec \<sharp>* P"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -

      obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* M"
                             and "(r \<bullet> xvec) \<sharp>* K" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                             and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                             and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinctPerm r"
        by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* K"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q"
                             and Sq: "set q \<subseteq> set A\<^sub>Q \<times> set(q \<bullet> A\<^sub>Q)"
        by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, K, r \<bullet> N, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* M"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')" 
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
        by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, r \<bullet> N, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)

      have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      
      from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)"
        by(simp add: freshChainSimps)

      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> Sr \<open>distinctPerm r\<close> \<open>xvec \<sharp>* P\<close> \<open>(r \<bullet> xvec) \<sharp>* P\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')"
        by(rule inputAlpha)
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close>
        by(rule_tac inputPermFrameSubject) (assumption | simp)+
      hence PTrans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
        by(simp add: eqvts)
  
      moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>  Sp \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close>
      have FrP: "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
        by(simp add: frameChainAlpha)
      moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)"  by simp
      
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> Sr \<open>(r \<bullet> xvec) \<sharp>* N\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')"
        by(simp add: boundOutputChainAlpha'' create_residual.simps)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(r \<bullet> xvec) \<sharp>* (p \<bullet> A\<^sub>P)\<close>
        by(rule_tac outputPermFrameSubject) (assumption | auto)
      hence QTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
        by(simp add: eqvts)
      moreover hence "distinct(r \<bullet> xvec)" by(force dest: boundOutputDistinct)
      moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>  Sq \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close>
      have FrQ: "extractFrame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
        by(simp add: frameChainAlpha)
      moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(q \<bullet> A\<^sub>Q)"  by simp
  
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<turnstile> (p \<bullet> q \<bullet> M) \<leftrightarrow> (p \<bullet> q \<bullet> K)"
        by(rule_tac chanEqClosed)+
      with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close>
           \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
           \<open>A\<^sub>Q \<sharp>* K\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close>  Sp Sq
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<turnstile> (q \<bullet> M) \<leftrightarrow> (p \<bullet> K)" by(simp add: eqvts freshChainSimps)
      moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
      moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)" 
        by(simp add: freshChainSimps)
      moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> 
      moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)"
        by(simp add: freshChainSimps)
      moreover note  \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
                     \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
      moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
        by(simp add: freshChainSimps)
      moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)\<close>\<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q\<close> 
      moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
        by(simp add: freshChainSimps)
      moreover note  \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<close>
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
        by(simp add: freshChainSimps)
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
        by(simp add: freshChainSimps)
      moreover note \<open>(r \<bullet> xvec) \<sharp>* P\<close> 
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"
      by(simp add: freshChainSimps)
      moreover note \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"  
        by(simp add: freshChainSimps)
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))"
        by(rule_tac cComm1)
      with \<open>(r \<bullet> xvec) \<sharp>* P'\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close> Sr 
      show ?thesis
        by(subst resChainAlpha) auto
    qed
  }
  note Goal = this
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>P' where "extractFrame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* M" and "A\<^sub>P' \<sharp>* A\<^sub>Q"
    by(rule_tac C="(\<Psi>, P, Q, M, A\<^sub>Q)" in distinctFrame) auto
  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>Q' where "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* K" and "A\<^sub>P' \<sharp>* A\<^sub>Q'"
    apply(rule_tac C="(\<Psi>, P, Q, K, A\<^sub>P')" in distinctFrame) by auto
  ultimately show ?thesis using \<open>xvec \<sharp>* P\<close>
    by(rule_tac Goal) 
qed
 
lemma Comm2:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   Q'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  
  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* K"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
proof -
  {
    fix \<Psi>    :: 'b
    and \<Psi>\<^sub>Q  :: 'b
    and P    :: "('a, 'b, 'c) psi"
    and M    :: 'a
    and xvec :: "name list"
    and N    :: 'a
    and P'   :: "('a, 'b, 'c) psi"
    and A\<^sub>P   :: "name list"
    and \<Psi>\<^sub>P  :: 'b
    and Q    :: "('a, 'b, 'c) psi"
    and K    :: 'a
    and Q'   :: "('a, 'b, 'c) psi"
    and A\<^sub>Q   :: "name list"
 
    assume "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    and    "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
    and    "distinct A\<^sub>P"
    and    "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
    and    "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
    and    "distinct A\<^sub>Q"
    and    "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    and    "A\<^sub>P \<sharp>* \<Psi>"
    and    "A\<^sub>P \<sharp>* P"
    and    "A\<^sub>P \<sharp>* Q"
    and    "A\<^sub>P \<sharp>* M"
    and    "A\<^sub>P \<sharp>* A\<^sub>Q"
    and    "A\<^sub>Q \<sharp>* \<Psi>"
    and    "A\<^sub>Q \<sharp>* P"
    and    "A\<^sub>Q \<sharp>* Q"
    and    "A\<^sub>Q \<sharp>* K"
    and    "xvec \<sharp>* Q"

    have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')"
    proof -

      obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* M"
                             and "(r \<bullet> xvec) \<sharp>* K" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                             and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                             and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinctPerm r"
        by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* K"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
                             and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q"
                             and Sq: "set q \<subseteq> set A\<^sub>Q \<times> set(q \<bullet> A\<^sub>Q)"
        by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, K, r \<bullet> N, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)
      obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* M"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')" 
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
                             and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
        by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, r \<bullet> N, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, r \<bullet> Q', r \<bullet> P')" in name_list_avoiding)
          (auto simp add: eqvts fresh_star_prod)

      have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
      have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
      
      from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
        by(drule_tac extractFrameFreshChain) auto
      from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
        by(drule_tac extractFrameFreshChain) auto

      from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> A\<^sub>Q)"
        by(simp add: freshChainSimps)
  
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> Sr \<open>(r \<bullet> xvec) \<sharp>* N\<close> \<open>(r \<bullet> xvec) \<sharp>* P'\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')"
        by(simp add: boundOutputChainAlpha'' create_residual.simps)
      hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(r \<bullet> xvec) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
        by(rule_tac outputPermFrameSubject) (assumption | auto)
      hence PTrans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
        by(simp add: eqvts)
      moreover hence "distinct(r \<bullet> xvec)" by(force dest: boundOutputDistinct)
  
      moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>  Sp \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close>
      have FrP: "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
        by(simp add: frameChainAlpha)
      moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)"  by simp
      
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> Sr \<open>distinctPerm r\<close> \<open>xvec \<sharp>* Q\<close> \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')"
        by(rule inputAlpha)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close>
        by(rule_tac inputPermFrameSubject) (assumption | simp)+
      hence QTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
        by(simp add: eqvts)
  
      moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>  Sq \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close>
      have FrQ: "extractFrame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
        by(simp add: frameChainAlpha)
      moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(q \<bullet> A\<^sub>Q)"  by simp
  
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<turnstile> (p \<bullet> q \<bullet> M) \<leftrightarrow> (p \<bullet> q \<bullet> K)"
        by(rule_tac chanEqClosed)+
      with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close>
           \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
           \<open>A\<^sub>Q \<sharp>* K\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close>  Sp Sq
      have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<turnstile> (q \<bullet> M) \<leftrightarrow> (p \<bullet> K)"
        by(simp add: eqvts freshChainSimps)
      moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
      moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)" 
        by(simp add: freshChainSimps)
      moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> 
      moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)" 
        by(simp add: freshChainSimps)
      moreover note  \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
                     \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
      moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
        by(simp add: freshChainSimps)
      moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)\<close>\<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q\<close> 
      moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
        by(simp add: freshChainSimps)
      moreover note  \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<close>
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" 
        by(simp add: freshChainSimps)
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
        by(simp add: freshChainSimps)
      moreover note \<open>(r \<bullet> xvec) \<sharp>* P\<close>
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"  
        by(simp add: freshChainSimps)
      moreover note \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
      moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"
        by(simp add: freshChainSimps)
      ultimately have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))"
        by(rule_tac cComm2)
      with \<open>(r \<bullet> xvec) \<sharp>* P'\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close> Sr 
      show ?thesis
        by(subst resChainAlpha) auto
    qed
  }
  note Goal = this
  note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>P' where "extractFrame P = \<langle>A\<^sub>P', \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P'" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* P" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* M" and "A\<^sub>P' \<sharp>* A\<^sub>Q"
    by(rule_tac C="(\<Psi>, P, Q, M, A\<^sub>Q)" in distinctFrame) auto
  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>Q' where "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* K" and "A\<^sub>P' \<sharp>* A\<^sub>Q'"
    by(rule_tac C="(\<Psi>, P, Q, K, A\<^sub>P')" in distinctFrame) auto
  ultimately show ?thesis using \<open>xvec \<sharp>* Q\<close>
    by(rule_tac Goal) 
qed

lemma semanticsCasesAux[consumes 1, case_names cInput cOutput cCase cPar1 cPar2 cComm1 cComm2 cOpen cScope cBang]:
  fixes \<Psi>  :: 'b
  and   cP  :: "('a, 'b, 'c) psi"
  and   cRs :: "('a, 'b, 'c) residual"
  and   C   :: "'d::fs_name"
  and   x   :: name

  assumes "\<Psi> \<rhd> cP \<longmapsto> cRs"
  and     rInput: "\<And>M K xvec N Tvec P. \<lbrakk>cP = M\<lparr>\<lambda>*xvec N\<rparr>.P;  cRs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec];
                                            \<Psi> \<turnstile> M \<leftrightarrow> K; distinct xvec; set xvec \<subseteq> supp N; length xvec=length Tvec;
                                            xvec \<sharp>* Tvec; xvec \<sharp>* \<Psi>; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop"
  and     rOutput: "\<And>M K N P. \<lbrakk>cP = M\<langle>N\<rangle>.P; cRs = K\<langle>N\<rangle> \<prec> P; \<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop"
  and     rCase: "\<And>Cs P \<phi>. \<lbrakk>cP = Cases Cs; \<Psi> \<rhd> P \<longmapsto> cRs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"

  and  rPar1: "\<And>\<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q. \<lbrakk>cP = P \<parallel> Q; cRs = \<alpha> \<prec> (P' \<parallel> Q);
               (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto> (\<alpha> \<prec> P'); extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
               A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* C; A\<^sub>Q \<sharp>* P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha>  \<sharp>* \<Psi>\<^sub>Q; 
               bn \<alpha>  \<sharp>* Q; bn \<alpha>  \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
               Prop"
  and     rPar2:   "\<And>\<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P. \<lbrakk>cP = P \<parallel> Q; cRs = \<alpha> \<prec> (P \<parallel> Q');
                      (\<Psi> \<otimes> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
             A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* C;
             A\<^sub>P \<sharp>* Q'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* \<Psi>\<^sub>P; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* Q; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop"
             
  and     rComm1: "\<And>\<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q.
                   \<lbrakk>cP = P \<parallel> Q; cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop"
  and     rComm2: "\<And>\<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q.
                   \<lbrakk>cP = P \<parallel> Q; cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop"
  and    rOpen: "\<And>P M xvec yvec N P' x.
                \<lbrakk>cP = \<lparr>\<nu>x\<rparr>P; cRs = M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; 
                 \<Psi> \<rhd> P \<longmapsto> M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; x \<in> supp N; x \<sharp> xvec; x \<sharp> yvec; x \<sharp> M; x \<sharp> \<Psi>; distinct xvec; distinct yvec;
                 xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* yvec; yvec \<sharp>* \<Psi>; yvec \<sharp>* P; yvec \<sharp>* M; xvec \<sharp>* C; x \<sharp> C; yvec \<sharp>* C\<rbrakk> \<Longrightarrow>
                 Prop"
  and    rScope: "\<And>P \<alpha> P' x. \<lbrakk>cP = \<lparr>\<nu>x\<rparr>P; cRs = \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P';
                                 \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; x \<sharp> \<Psi>; x \<sharp> \<alpha>; x \<sharp> C; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop"
  and    rBang:  "\<And>P. \<lbrakk>cP = !P; \<Psi> \<rhd> P \<parallel> !P \<longmapsto> cRs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  shows Prop
using \<open>\<Psi> \<rhd> cP \<longmapsto> cRs\<close>
proof(cases rule: semantics.cases)
  case(cInput M K xvec N Tvec P)
  obtain p::"name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* K"
                         and "(p \<bullet> xvec) \<sharp>* Tvec" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* C"
                         and S: "(set p) \<subseteq> (set xvec) \<times> (set(p \<bullet> xvec))" and "distinctPerm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, K, N, P, C, Tvec)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)
    from \<open>cP = M\<lparr>\<lambda>*xvec N\<rparr>.P\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S
    have "cP = M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P)"
      by(simp add: inputChainAlpha')
    moreover from \<open>cRs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S \<open>length xvec = length Tvec\<close> \<open>distinctPerm p\<close>
    have "cRs = K\<lparr>((p \<bullet> N)[(p \<bullet> xvec)::=Tvec])\<rparr> \<prec> (p \<bullet> P)[(p \<bullet> xvec)::=Tvec]"
      by(auto simp add: substTerm.renaming renaming residualInject)
    
    moreover note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close>
    moreover from \<open>distinct xvec\<close> have "distinct(p \<bullet> xvec)"
      by simp
    moreover from \<open>(set xvec) \<subseteq> (supp N)\<close> have "(p \<bullet> (set xvec)) \<subseteq> (p \<bullet> (supp N))"
      by simp
    hence "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
      by(simp add: eqvts)
    moreover from \<open>length xvec = length Tvec\<close> have "length(p \<bullet> xvec) = length Tvec"
      by simp
  ultimately show ?thesis using \<open>(p \<bullet> xvec) \<sharp>* Tvec\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>(p \<bullet> xvec) \<sharp>* K\<close>
                                \<open>(p \<bullet> xvec) \<sharp>* C\<close>
    by(rule rInput)
next
  case(Output M K N P)
  thus ?thesis by(rule rOutput)
next
  case(Case P \<phi> Cs)
  thus ?thesis by(rule rCase)
next
  case(cPar1 \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q)
  obtain q::"name prm" where "(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* P" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Q" 
                         and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>Q" and "(bn(q \<bullet> \<alpha>)) \<sharp>* P'" and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>Q"
                         and "distinctPerm q"
                         and "(bn(q \<bullet> \<alpha>)) \<sharp>* C" and Sq: "(set q) \<subseteq> set(bn \<alpha>) \<times> (set(bn(q \<bullet> \<alpha>)))"
    by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>Q, \<Psi>\<^sub>Q, P', C)" in name_list_avoiding) (auto simp add: eqvts)
  obtain p::"name prm" where "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>Q) \<sharp>* P" and "(p \<bullet> A\<^sub>Q) \<sharp>* Q" 
                         and "(p \<bullet> A\<^sub>Q) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>Q) \<sharp>* P'" 
                         and "(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')" and "(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>Q) \<sharp>* C" 
                         and Sp: "(set p) \<subseteq> (set A\<^sub>Q) \<times> (set(p \<bullet> A\<^sub>Q))" and "distinctPerm p"
    by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, \<alpha>, q \<bullet> \<alpha>, P', (q \<bullet> P'), \<Psi>\<^sub>Q, C)" in name_list_avoiding) auto
  from \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>Q\<close> Sq \<open>distinctPerm q\<close> have "A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)"
    by(subst fresh_star_bij[symmetric, of _ _  q]) (simp add: eqvts)
  from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinctPerm q\<close> have "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)"
    by(subst fresh_star_bij[symmetric, of _ _  q]) (simp add: eqvts)
  from \<open>distinct(bn \<alpha>)\<close> \<open>distinctPerm q\<close> have "distinct(bn(q \<bullet> \<alpha>))" 
    by(subst distinctClosed[symmetric, of _ q]) (simp add: eqvts)
  note \<open>cP = P \<parallel> Q\<close>

  moreover from \<open>cRs = \<alpha> \<prec> (P' \<parallel> Q)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P'\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* Q\<close> Sq
  have "cRs = (q \<bullet> \<alpha>) \<prec> (q \<bullet> P') \<parallel> Q"
    by(force simp add: residualAlpha)
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P'\<close> Sq
  have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> P')"
    by(force simp add: residualAlpha)
  hence "A\<^sub>Q \<sharp>* (q \<bullet> P')" using \<open>bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)\<close>
    by(drule_tac freeFreshChainDerivative) auto

  from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> (p \<bullet> P) \<longmapsto>p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> P'))"
    by(rule semantics.eqvt)
  with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>A\<^sub>Q \<sharp>* (q \<bullet> P')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>Q\<close>  \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close>
       \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* P\<close>  \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')\<close> Sp
  have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> P')" by(simp add: eqvts)
  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close> Sp have  "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), (p \<bullet> \<Psi>\<^sub>Q)\<rangle>"
    by(simp add: frameChainAlpha' eqvts)
  moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close> Sp have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)"
    by(simp add: freshAlphaPerm)
  moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>Q)" by simp
  ultimately show ?thesis
    using \<open>(p \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> \<alpha>)\<close>
          \<open>(p \<bullet> A\<^sub>Q) \<sharp>* (q \<bullet> P')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P\<close>
          \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* C\<close> \<open>(p \<bullet> A\<^sub>Q) \<sharp>* C\<close> \<open>bn (q \<bullet> \<alpha>) \<sharp>* subject (q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close>
    by(rule_tac rPar1)
next
  case(cPar2 \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P)
  obtain q::"name prm" where "(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* P" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Q" 
                         and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>P" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Q'" and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>P"
                         and "distinctPerm q"
                         and "(bn(q \<bullet> \<alpha>)) \<sharp>* C" and Sq: "(set q) \<subseteq> set(bn \<alpha>) \<times> (set(bn(q \<bullet> \<alpha>)))"
    by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, Q, \<alpha>, A\<^sub>P, \<Psi>\<^sub>P, Q', C)" in name_list_avoiding) (auto simp add: eqvts)
  obtain p::"name prm" where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" 
                         and "(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>" and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)" and "(p \<bullet> A\<^sub>P) \<sharp>* Q'" 
                         and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* C" 
                         and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))" and "distinctPerm p"
    by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, \<alpha>, q \<bullet> \<alpha>, Q', (q \<bullet> Q'), \<Psi>\<^sub>P, C)" in name_list_avoiding) auto
  from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>bn(q \<bullet> \<alpha>) \<sharp>* A\<^sub>P\<close> Sq \<open>distinctPerm q\<close> have "A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)"
    by(subst fresh_star_bij[symmetric, of _ _  q]) (simp add: eqvts)
  from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinctPerm q\<close> have "bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)"
    by(subst fresh_star_bij[symmetric, of _ _  q]) (simp add: eqvts)
  from \<open>distinct(bn \<alpha>)\<close> \<open>distinctPerm q\<close> have "distinct(bn(q \<bullet> \<alpha>))" 
    by(subst distinctClosed[symmetric, of _ q]) (simp add: eqvts)
  note \<open>cP = P \<parallel> Q\<close>

  moreover from \<open>cRs = \<alpha> \<prec> (P \<parallel> Q')\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q'\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* P\<close> Sq
  have "cRs = (q \<bullet> \<alpha>) \<prec> P \<parallel>  (q \<bullet> Q')"
    by(force simp add: residualAlpha)
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q'\<close> Sq
  have Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')"
    by(force simp add: residualAlpha)
  hence "A\<^sub>P \<sharp>* (q \<bullet> Q')" using \<open>bn(q \<bullet> \<alpha>) \<sharp>* subject(q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)\<close>
    by(drule_tac freeFreshChainDerivative) auto

  from Trans have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> (p \<bullet> Q) \<longmapsto>p \<bullet> ((q \<bullet> \<alpha>) \<prec> (q \<bullet> Q'))"
    by(rule semantics.eqvt)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> \<alpha>)\<close> \<open>A\<^sub>P \<sharp>* (q \<bullet> Q')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>P\<close>  \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close>
       \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close>  \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')\<close> Sp
  have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(q \<bullet> \<alpha>) \<prec> (q \<bullet> Q')" by(simp add: eqvts)
  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close> Sp have  "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
    by(simp add: frameChainAlpha' eqvts)
  moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close> Sp have "(bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
    by(simp add: freshAlphaPerm)
  moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)" by simp
  ultimately show ?thesis
    using \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<alpha>)\<close>
          \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> Q')\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<Psi>\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Q\<close> \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P\<close>
          \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* C\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* C\<close> \<open>bn (q \<bullet> \<alpha>) \<sharp>* subject (q \<bullet> \<alpha>)\<close> \<open>distinct(bn(q \<bullet> \<alpha>))\<close>
    by(rule_tac rPar2)
next
  case(cComm1 \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q)
  obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* M"
                         and "(r \<bullet> xvec) \<sharp>* K" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                         and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                         and "(r \<bullet> xvec) \<sharp>* C" and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinctPerm r"
    by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q', C)" in name_list_avoiding)
      (auto simp add: eqvts)

  obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* K"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* N" and "(q \<bullet> A\<^sub>Q) \<sharp>* xvec" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q'" and "(q \<bullet> A\<^sub>Q) \<sharp>* P'"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and  "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* C" and Sq: "(set q) \<subseteq> (set A\<^sub>Q) \<times> (set(q \<bullet> A\<^sub>Q))"
    by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, K, N, xvec, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, Q', P', C)" in name_list_avoiding) clarsimp
  
  obtain p::"name prm"  where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* M"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* N" and "(p \<bullet> A\<^sub>P) \<sharp>* xvec" and "(p \<bullet> A\<^sub>P) \<sharp>* Q'" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* P'" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* C" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
    by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, N, xvec, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, Q', P', C)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  
  from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(drule_tac extractFrameFreshChain) auto
  from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(drule_tac extractFrameFreshChain) auto
  note \<open>cP = P \<parallel> Q\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* P'\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close> have "(r \<bullet> xvec) \<sharp>* (P' \<parallel> Q')"
    by simp
  with \<open>cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')\<close> \<open>(r \<bullet> xvec) \<sharp>* N\<close> Sr
  have "cRs = \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>(r \<bullet> (P' \<parallel> Q'))" by(simp add: resChainAlpha residualInject)
  hence "cRs = \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))" by simp
  
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> Sr \<open>distinctPerm r\<close> \<open>xvec \<sharp>* P\<close> \<open>(r \<bullet> xvec) \<sharp>* P\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')"
    by(rule inputAlpha)
  hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close>
    by(rule_tac inputPermFrameSubject) (assumption | simp)+
  hence PTrans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
    by(simp add: eqvts)
  
  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>  Sp \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close>
  have FrP: "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
    by(simp add: frameChainAlpha)
  moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)"  by simp

  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> Sr \<open>(r \<bullet> xvec) \<sharp>* N\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')"
    by(simp add: boundOutputChainAlpha'' residualInject)
  hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close>\<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close>
    by(rule_tac outputPermFrameSubject) (assumption | auto)

  hence QTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
    by(simp add: eqvts)
  
  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>  Sq \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close>
  have FrQ: "extractFrame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
    by(simp add: frameChainAlpha)
  moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(q \<bullet> A\<^sub>Q)"  by simp
  
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<turnstile> (p \<bullet> q \<bullet> M) \<leftrightarrow> (p \<bullet> q \<bullet> K)"
    by(rule_tac chanEqClosed)+
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close>
       \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
       \<open>A\<^sub>Q \<sharp>* K\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close>  Sp Sq
  have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<turnstile> (q \<bullet> M) \<leftrightarrow> (p \<bullet> K)"
    by(simp add: eqvts freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> 
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)" 
    by(simp add: freshChainSimps)
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* N\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" 
    by(simp add: freshChainSimps)
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')" 
    by(simp add: freshChainSimps)
  moreover note  \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close>
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q'\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')"
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> 
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
    by(simp add: freshChainSimps)
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* N\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)" 
    by(simp add: freshChainSimps)
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P'\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q\<close> 
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q'\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"  
    by(simp add: freshChainSimps)
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"  
    by(simp add: freshChainSimps)
  moreover note \<open>(r \<bullet> xvec) \<sharp>* P\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"  
    by(simp add: freshChainSimps)
  moreover note \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"  
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* C\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* C\<close> \<open>(r \<bullet> xvec) \<sharp>* C\<close> 
  moreover from \<open>distinct xvec\<close> have "distinct(r \<bullet> xvec)" by simp
  ultimately show ?thesis by(rule rComm1) 
next
  case(cComm2 \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q)
  obtain r::"name prm" where "(r \<bullet> xvec) \<sharp>* \<Psi>" and "(r \<bullet> xvec) \<sharp>* P" and "(r \<bullet> xvec) \<sharp>* Q" and "(r \<bullet> xvec) \<sharp>* M"
    and "(r \<bullet> xvec) \<sharp>* K" and "(r \<bullet> xvec) \<sharp>* N" and "(r \<bullet> xvec) \<sharp>* A\<^sub>P" and "(r \<bullet> xvec) \<sharp>* A\<^sub>Q"
                         and "(r \<bullet> xvec) \<sharp>* P'" and "(r \<bullet> xvec) \<sharp>* Q'" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                         and "(r \<bullet> xvec) \<sharp>* C" and Sr: "(set r) \<subseteq> (set xvec) \<times> (set(r \<bullet> xvec))" and "distinctPerm r"
    by(rule_tac xvec=xvec and c="(\<Psi>, P, Q, M, K, N, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P, \<Psi>\<^sub>Q, P', Q', C)" in name_list_avoiding)
      (auto simp add: eqvts)

  obtain q::"name prm" where "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>" and "(q \<bullet> A\<^sub>Q) \<sharp>* P" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* K"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* N" and "(q \<bullet> A\<^sub>Q) \<sharp>* xvec" and "(q \<bullet> A\<^sub>Q) \<sharp>* Q'" and "(q \<bullet> A\<^sub>Q) \<sharp>* P'"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P" and  "(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P" and "(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q" and "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)"
                         and "(q \<bullet> A\<^sub>Q) \<sharp>* C" and Sq: "(set q) \<subseteq> (set A\<^sub>Q) \<times> (set(q \<bullet> A\<^sub>Q))"
    by(rule_tac xvec=A\<^sub>Q and c="(\<Psi>, P, Q, K, N, xvec, r \<bullet> xvec, \<Psi>\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>P, Q', P', C)" in name_list_avoiding) clarsimp
  
  obtain p::"name prm"  where "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>P) \<sharp>* P" and "(p \<bullet> A\<^sub>P) \<sharp>* Q" and "(p \<bullet> A\<^sub>P) \<sharp>* M"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* N" and "(p \<bullet> A\<^sub>P) \<sharp>* xvec" and "(p \<bullet> A\<^sub>P) \<sharp>* Q'" and "(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* P'" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)"
                          and "(p \<bullet> A\<^sub>P) \<sharp>* C" and "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)" and Sp: "(set p) \<subseteq> (set A\<^sub>P) \<times> (set(p \<bullet> A\<^sub>P))"
    by(rule_tac xvec=A\<^sub>P and c="(\<Psi>, P, Q, M, N, xvec, r \<bullet> xvec, A\<^sub>Q, q \<bullet> A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, Q', P', C)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  
  from \<open>A\<^sub>P \<sharp>* Q\<close> FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(drule_tac extractFrameFreshChain) auto
  from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(drule_tac extractFrameFreshChain) auto
  
  note \<open>cP = P \<parallel> Q\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* P'\<close> \<open>(r \<bullet> xvec) \<sharp>* Q'\<close> have "(r \<bullet> xvec) \<sharp>* (P' \<parallel> Q')"
    by simp
  with \<open>cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')\<close> \<open>(r \<bullet> xvec) \<sharp>* N\<close> Sr
  have "cRs = \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>(r \<bullet> (P' \<parallel> Q'))" by(simp add: resChainAlpha residualInject)
  hence "cRs = \<tau> \<prec> \<lparr>\<nu>*(r \<bullet> xvec)\<rparr>((r \<bullet> P') \<parallel> (r \<bullet> Q'))"
    by simp
  
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> Sr \<open>(r \<bullet> xvec) \<sharp>* N\<close> \<open>(r \<bullet> xvec) \<sharp>* P'\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" by(simp add: boundOutputChainAlpha'' residualInject)
  hence "(q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close>
    by(rule_tac outputPermFrameSubject) (assumption | auto)
  hence PTrans: "\<Psi> \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>(q \<bullet> M)\<lparr>\<nu>*(r \<bullet> xvec)\<rparr>\<langle>(r \<bullet> N)\<rangle> \<prec> (r \<bullet> P')" using Sq \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
    by(simp add: eqvts)
  
  moreover from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>  Sp \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>P\<close>
  have FrP: "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), (p \<bullet> \<Psi>\<^sub>P)\<rangle>"
    by(simp add: frameChainAlpha)
  moreover from \<open>distinct A\<^sub>P\<close> have "distinct(p \<bullet> A\<^sub>P)"  by simp

  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> Sr  \<open>distinctPerm r\<close> \<open>xvec \<sharp>* Q\<close> \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" by(rule inputAlpha)
  hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close>
    by(rule_tac inputPermFrameSubject) (assumption | simp)+
  hence QTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>(p \<bullet> K)\<lparr>(r \<bullet> N)\<rparr> \<prec> (r \<bullet> Q')" using Sp \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
    by(simp add: eqvts)
  
  moreover from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>  Sq \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>Q\<close>
  have FrQ: "extractFrame Q = \<langle>(q \<bullet> A\<^sub>Q), (q \<bullet> \<Psi>\<^sub>Q)\<rangle>"
    by(simp add: frameChainAlpha)
  moreover from \<open>distinct A\<^sub>Q\<close> have "distinct(q \<bullet> A\<^sub>Q)"  by simp
  
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> q \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<turnstile> (p \<bullet> q \<bullet> M) \<leftrightarrow> (p \<bullet> q \<bullet> K)"
    by(rule_tac chanEqClosed)+
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close>
       \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close>
       \<open>A\<^sub>Q \<sharp>* K\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close>  Sp Sq
  have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<otimes> (q \<bullet> \<Psi>\<^sub>Q) \<turnstile> (q \<bullet> M) \<leftrightarrow> (p \<bullet> K)"
    by(simp add: eqvts freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close>
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)" 
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* P\<close> 
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> Sq have "(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> M)" 
    by(simp add: freshChainSimps)
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* N\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> N)" 
    by(simp add: freshChainSimps)
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> P')"
    by(simp add: freshChainSimps)
  moreover note  \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q\<close>
  moreover from \<open>(p \<bullet> A\<^sub>P) \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Q'\<close> Sr have "(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> Q')"
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<close>
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P\<close> 
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (q \<bullet> A\<^sub>Q)\<close> Sp Sq have "(q \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> K)"
    by(simp add: freshChainSimps)
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* N\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> N)"
    by(simp add: freshChainSimps)
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* P'\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> P')"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q\<close> 
  moreover from \<open>(q \<bullet> A\<^sub>Q) \<sharp>* xvec\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* Q'\<close> Sr have "(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> Q')"
    by(simp add: freshChainSimps)
  moreover note \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)"  
    by(simp add: freshChainSimps)
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> \<Psi>\<^sub>Q)"
    by(simp add: freshChainSimps)
  moreover note \<open>(r \<bullet> xvec) \<sharp>* P\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* M\<close> Sq have "(r \<bullet> xvec) \<sharp>* (q \<bullet> M)"  
    by(simp add: freshChainSimps)
  moreover note \<open>(r \<bullet> xvec) \<sharp>* Q\<close>
  moreover from \<open>(r \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* (r \<bullet> xvec)\<close> \<open>(r \<bullet> xvec) \<sharp>* K\<close> Sp have "(r \<bullet> xvec) \<sharp>* (p \<bullet> K)"  
    by(simp add: freshChainSimps)
  moreover note \<open>(p \<bullet> A\<^sub>P) \<sharp>* C\<close> \<open>(q \<bullet> A\<^sub>Q) \<sharp>* C\<close> \<open>(r \<bullet> xvec) \<sharp>* C\<close>
  moreover from \<open>distinct xvec\<close> have "distinct(r \<bullet> xvec)" by simp
  ultimately show ?thesis by(rule rComm2) 
next
  case(cOpen P M xvec yvec N P' x)
  from \<open>\<Psi> \<rhd> P \<longmapsto> M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close>  have "distinct(xvec@yvec)" by(force dest: boundOutputDistinct)
  hence "xvec \<sharp>* yvec" by(induct xvec) auto
  obtain p where "(p \<bullet> yvec) \<sharp>* \<Psi>" and "(p \<bullet> yvec) \<sharp>* P"  and "(p \<bullet> yvec) \<sharp>* M"
             and "(p \<bullet> yvec) \<sharp>* yvec" and "(p \<bullet> yvec) \<sharp>* N" and "(p \<bullet> yvec) \<sharp>* P'"
             and "x \<sharp> (p \<bullet> yvec)" and "(p \<bullet> yvec) \<sharp>* xvec"
             and "(p \<bullet> yvec) \<sharp>* C" and Sp: "(set p) \<subseteq> (set yvec) \<times> (set(p \<bullet> yvec))"
    by(rule_tac xvec=yvec and c="(\<Psi>, P, M, xvec, yvec, N, P', x, C)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod) 
  obtain q where "(q \<bullet> xvec) \<sharp>* \<Psi>" and "(q \<bullet> xvec) \<sharp>* P"  and "(q \<bullet> xvec) \<sharp>* M"
             and "(q \<bullet> xvec) \<sharp>* xvec" and "(q \<bullet> xvec) \<sharp>* N" and "(q \<bullet> xvec) \<sharp>* P'"
             and "x \<sharp> (q \<bullet> xvec)" and "(q \<bullet> xvec) \<sharp>* yvec" 
             and "(q \<bullet> xvec) \<sharp>* p" and "(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)"
             and "(q \<bullet> xvec) \<sharp>* C" and Sq: "(set q) \<subseteq> (set xvec) \<times> (set(q \<bullet> xvec))"
    by(rule_tac xvec=xvec and c="(\<Psi>, P, M, xvec, yvec, p \<bullet> yvec, N, P', x, p, C)" in name_list_avoiding)
      (auto simp add: eqvts fresh_star_prod)
  obtain y::name where "y \<sharp> P" and "y \<sharp> C" and "y \<sharp> xvec" and "y \<sharp> yvec" and "y \<noteq> x" and "y \<sharp> N" 
                   and "y \<sharp> (q \<bullet> xvec)" and "y \<sharp> (p \<bullet> yvec)" and "y \<sharp> M" and "y \<sharp> \<Psi>" and "y \<sharp> P'"
    by(generate_fresh "name") (auto simp add: freshChainSimps)

  from \<open>cP = \<lparr>\<nu>x\<rparr>P\<close> \<open>y \<sharp> P\<close> have "cP = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by(simp add: alphaRes)
  moreover have "cRs = M\<lparr>\<nu>*((q \<bullet> xvec)@y#(p \<bullet> yvec))\<rparr>\<langle>((q@(x, y)#p) \<bullet> N)\<rangle> \<prec> ((q@(x, y)#p) \<bullet> P')"
  proof -
    note \<open>cRs = M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
    moreover have "\<lparr>\<nu>*(xvec@x#yvec)\<rparr>N \<prec>' P' = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*yvec\<rparr>N \<prec>' P'))" by(simp add: boundOutputApp)
    moreover from \<open>(p \<bullet> yvec) \<sharp>* N\<close> \<open>(p \<bullet> yvec) \<sharp>* P'\<close> Sp have "\<dots> = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(p \<bullet> N) \<prec>' (p \<bullet> P')))"
      by(simp add: boundOutputChainAlpha'')
    moreover with \<open>y \<sharp> N\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> (p \<bullet> yvec)\<close> \<open>y \<sharp> yvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> Sp
    have "\<dots> = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>(([(x, y)] \<bullet> p \<bullet> N) \<prec>' ([(x, y)] \<bullet> p \<bullet> P'))))"
      by(subst alphaBoundOutput[where y=y]) (simp add: freshChainSimps eqvts)+
    moreover hence "\<dots> = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>((((x, y)#p) \<bullet> N) \<prec>' (((x, y)#p) \<bullet> P'))))"
      by simp
    moreover from \<open>(q \<bullet> xvec) \<sharp>* N\<close> \<open>(q \<bullet> xvec) \<sharp>* P'\<close> \<open>xvec \<sharp>* yvec\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> 
                  \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> (q \<bullet> xvec)\<close> Sp Sq
    have "\<dots> = \<lparr>\<nu>*(q \<bullet> xvec)\<rparr>(\<lparr>\<nu>y\<rparr>(\<lparr>\<nu>*(p \<bullet> yvec)\<rparr>((q \<bullet> ((x, y)#p) \<bullet> N) \<prec>' (q \<bullet> ((x, y)#p) \<bullet> P'))))"
      apply(subst boundOutputChainAlpha[where p=q and xvec=xvec and yvec="xvec"])
      defer
      apply assumption
      apply simp
      apply(simp add: eqvts)
      apply(simp add: eqvts)
      apply(simp add: boundOutputFreshSet(4))
      apply(rule conjI)
      apply(simp add: freshChainSimps)
      apply(simp add: freshChainSimps)
      done
    moreover hence "\<dots> = \<lparr>\<nu>*(q \<bullet> xvec@y#(p \<bullet> yvec))\<rparr>((q@(x, y)#p) \<bullet> N) \<prec>' ((q@(x, y)#p) \<bullet> P')"
      by(simp only: pt2[OF pt_name_inst] boundOutputApp BOresChain.simps)
    ultimately show ?thesis
      by(simp only: residualInject)
  qed
  moreover have "\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*((q \<bullet> xvec)@(p \<bullet> yvec))\<rparr>\<langle>((q@(x, y)#p) \<bullet> N)\<rangle> \<prec> ((q@(x, y)#p) \<bullet> P')"
  proof -
    note\<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
    moreover from \<open>(p \<bullet> yvec) \<sharp>* N\<close> \<open>(q \<bullet> xvec) \<sharp>* N\<close> \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> Sp Sq 
    have "((q@p) \<bullet> (xvec @ yvec)) \<sharp>* N" apply(simp only: eqvts) apply(simp only: pt2[OF pt_name_inst])
      by simp
    moreover from \<open>(p \<bullet> yvec) \<sharp>* P'\<close> \<open>(q \<bullet> xvec) \<sharp>* P'\<close> \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close> Sp Sq 
    have "((q@p) \<bullet> (xvec @ yvec)) \<sharp>* P'" by(simp del: freshAlphaPerm add: eqvts pt2[OF pt_name_inst])
    moreover from Sp Sq \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close>
    have Spq: "set(q@p) \<subseteq> set(xvec@yvec) \<times> set((q@p) \<bullet> (xvec@yvec))"
      by(simp add: pt2[OF pt_name_inst] eqvts) blast
    ultimately have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*((q@p) \<bullet> (xvec@yvec))\<rparr>\<langle>((q@p) \<bullet> N)\<rangle> \<prec> ((q@p) \<bullet> P')"
      apply(simp only: residualInject)
      by(erule_tac rev_mp) (subst boundOutputChainAlpha, auto)
    with  Sp Sq \<open>xvec \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* yvec\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close> \<open>(p \<bullet> yvec) \<sharp>* xvec\<close>
    have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*((q \<bullet> xvec)@(p \<bullet> yvec))\<rparr>\<langle>((q@p) \<bullet> N)\<rangle> \<prec> ((q@p) \<bullet> P')"
      by(simp add: eqvts pt2[OF pt_name_inst] del: freshAlphaPerm)
    hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<longmapsto> [(x, y)] \<bullet> (M\<lparr>\<nu>*((q \<bullet> xvec)@(p \<bullet> yvec))\<rparr>\<langle>((q@p) \<bullet> N)\<rangle> \<prec> ((q@p) \<bullet> P'))"
      by(rule semantics.eqvt)
    with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>y \<sharp> xvec\<close> \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>y \<sharp> (q \<bullet> xvec) \<close>\<open>x \<sharp> yvec\<close> \<open>y \<sharp> yvec\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> \<open>y \<sharp> (p \<bullet> yvec)\<close> Sp Sq
    show ?thesis 
      apply(simp add: eqvts pt2[OF pt_name_inst])
      by(subst perm_compose[of q], simp)+
  qed
  moreover from \<open>x \<in> supp N\<close> have "((q@(x, y)#p) \<bullet> x) \<in> ((q@(x, y)#p) \<bullet> (supp N))"
    by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> \<open>y \<sharp> xvec\<close> \<open>y \<sharp> (q \<bullet> xvec)\<close> Sp Sq
  have "y \<in> supp((q@(x, y)#p)\<bullet> N)" by(simp add: pt2[OF pt_name_inst] calc_atm eqvts)
  moreover from \<open>distinct xvec\<close> have "distinct(q \<bullet> xvec)" by simp
  moreover from \<open>distinct yvec\<close> have "distinct(p \<bullet> yvec)" by simp
  moreover note \<open>x \<sharp> (q \<bullet> xvec)\<close> \<open>x \<sharp> (p \<bullet> yvec)\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> \<Psi>\<close> 
                \<open>(q \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(q \<bullet> xvec) \<sharp>* P\<close> \<open>(q \<bullet> xvec) \<sharp>* M\<close> \<open>(q \<bullet> xvec) \<sharp>* (p \<bullet> yvec)\<close>
                \<open>(p \<bullet> yvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> yvec) \<sharp>* P\<close> \<open>(p \<bullet> yvec) \<sharp>* M\<close> \<open>y \<sharp> (q \<bullet> xvec)\<close> \<open>y \<sharp> (p \<bullet> yvec)\<close> \<open>y \<sharp> M\<close> \<open>y \<sharp> C\<close> \<open>y \<sharp> \<Psi>\<close>
                 \<open>(p \<bullet> yvec) \<sharp>* C\<close> \<open>(q \<bullet> xvec) \<sharp>* C\<close>
  ultimately show Prop by(rule_tac rOpen) (assumption | simp)+
next
  case(cScope P \<alpha> P' x)
  obtain p::"name prm" where "(bn(p \<bullet> \<alpha>)) \<sharp>* \<Psi>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P"
                         and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'" and "x \<sharp> bn(p \<bullet> \<alpha>)"
                         and "distinctPerm p"
                         and "(bn(p \<bullet> \<alpha>)) \<sharp>* C" and Sp: "(set p) \<subseteq> set(bn \<alpha>) \<times> (set(bn(p \<bullet> \<alpha>)))"
    by(rule_tac xvec="bn \<alpha>" and c="(\<Psi>, P, \<alpha>, x, P', C)" in name_list_avoiding) (auto simp add: eqvts)
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> (p \<bullet> P')" and "y \<sharp> (p \<bullet> \<alpha>)" and "y \<sharp> C"
    by(generate_fresh "name") (auto simp add: freshChainSimps simp del: actionFresh)
  from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinctPerm p\<close> have "bn(p \<bullet> \<alpha>) \<sharp>* subject(p \<bullet> \<alpha>)"
    by(subst fresh_star_bij[symmetric, of _ _  p]) (simp add: eqvts)
  from \<open>distinct(bn \<alpha>)\<close> \<open>distinctPerm p\<close> have "distinct(bn(p \<bullet> \<alpha>))" 
    by(subst distinctClosed[symmetric, of _ p]) (simp add: eqvts)
  from \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> (bn(p \<bullet> \<alpha>))\<close> \<open>distinctPerm p\<close> Sp have "x \<sharp> (p \<bullet> \<alpha>)"
    by(subst fresh_bij[symmetric, of _ _ p]) (simp add: eqvts freshChainSimps)

  moreover from \<open>cP = \<lparr>\<nu>x\<rparr>P\<close> \<open>y \<sharp> P\<close> have "cP = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)" by(simp add: alphaRes)
  moreover from \<open>cRs = \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>x \<sharp> bn(p \<bullet> \<alpha>)\<close> \<open>(bn(p \<bullet> \<alpha>)) \<sharp>* P'\<close> \<open>x \<sharp> \<alpha>\<close> Sp
  have "cRs = (p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P')"
    by(force simp add: residualAlpha)
  with \<open>y \<sharp> (p \<bullet> P')\<close> have "cRs = (p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> p \<bullet> P')"
    by(simp add: alphaRes)
  moreover from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> \<open>(bn(p \<bullet> \<alpha>)) \<sharp>* P'\<close> Sp
  have "\<Psi> \<rhd> P \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')" by(force simp add: residualAlpha)
  hence"([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>[(x, y)] \<bullet> ((p \<bullet> \<alpha>) \<prec> (p \<bullet> P'))"
    by(rule eqvts)
  with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> (p \<bullet> \<alpha>)\<close> \<open>x \<sharp> (p \<bullet> \<alpha>)\<close> Sp \<open>distinctPerm p\<close>
  have "\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>(p \<bullet> \<alpha>) \<prec> ([(x, y)] \<bullet> p \<bullet> P')" 
    by(simp add: eqvts)
  moreover from \<open>bn(p \<bullet> \<alpha>) \<sharp>* P\<close> \<open>y \<sharp> (p \<bullet> \<alpha>)\<close> \<open>y \<sharp> P\<close> have "bn(p \<bullet> \<alpha>) \<sharp>* ([(x, y)] \<bullet> P)"
    by(auto simp add: fresh_star_def fresh_left calc_atm) (simp add: fresh_def name_list_supp)
  moreover from \<open>distinct(bn \<alpha>)\<close> have "distinct(p \<bullet> bn \<alpha>)" by simp
  hence "distinct(bn(p \<bullet> \<alpha>))" by(simp add: eqvts)
  ultimately show ?thesis
    using \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> (p \<bullet> \<alpha>)\<close> \<open>y \<sharp> C\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* subject(p \<bullet> \<alpha>)\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* C\<close>
    by(rule_tac rScope)
next
  case(Bang P)
  thus ?thesis by(rule_tac rBang) 
qed

nominal_primrec
  inputLength :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> nat"
  and inputLength'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> nat"
  and inputLength'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase \<Rightarrow> nat"

where
  "inputLength (\<zero>) = 0"
| "inputLength (M\<langle>N\<rangle>.P) = 0"
| "inputLength (M\<lparr>I) = inputLength' I"
| "inputLength (Case C) = 0"
| "inputLength (P \<parallel> Q) = 0"
| "inputLength (\<lparr>\<nu>x\<rparr>P) = 0"
| "inputLength (\<lbrace>\<Psi>\<rbrace>) = 0"
| "inputLength (!P) = 0"

| "inputLength' (Trm M P) = 0"
| "inputLength' (\<nu> y I) = 1 + (inputLength' I)"

| "inputLength'' (\<bottom>\<^sub>c) = 0"
| "inputLength'' (\<box>\<Phi> \<Rightarrow> P C) = 0"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_nat)+

nominal_primrec boundOutputLength :: "('a, 'b, 'c) boundOutput \<Rightarrow> nat"
where
  "boundOutputLength (BOut M P) = 0"
| "boundOutputLength (BStep x B) = (boundOutputLength B) + 1"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_nat)+
  
nominal_primrec residualLength :: "('a, 'b, 'c) residual \<Rightarrow> nat"
where
  "residualLength (RIn M N P) = 0"
| "residualLength (ROut M B) = boundOutputLength B"
| "residualLength (RTau P) = 0"
by(rule TrueI)+

lemma inputLengthProc[simp]:
  shows "inputLength(M\<lparr>\<lambda>*xvec N\<rparr>.P) = length xvec"
by(induct xvec) auto

lemma boundOutputLengthSimp[simp]:
  shows "residualLength(M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P) = length xvec"
by(induct xvec) (auto simp add: residualInject)

lemma boundOuputLengthSimp2[simp]:
  shows "residualLength(\<alpha> \<prec> P) = length(bn \<alpha>)"
by(nominal_induct \<alpha> rule: action.strong_induct, auto) (auto simp add: residualInject)

lemmas [simp del] = inputLength_inputLength'_inputLength''.simps residualLength.simps boundOutputLength.simps

lemma constructPerm:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  
  assumes "length xvec = length yvec"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinctPerm p" and "yvec = p \<bullet> xvec"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinctPerm p; yvec = p \<bullet> xvec\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec"
  proof(induct n arbitrary: xvec yvec)
    case(0 xvec yvec)
    thus ?case by simp
  next
    case(Suc n xvec yvec)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>length xvec = length yvec\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "length xvec' = length yvec'" and "yvec = y#yvec'"
      by(case_tac yvec) auto
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    from \<open>Suc n = length xvec\<close> \<open>xvec=x#xvec'\<close> have "n = length xvec'" by simp
    with \<open>length xvec' = length yvec'\<close> \<open>xvec' \<sharp>* yvec'\<close> \<open>distinct xvec'\<close> \<open>distinct yvec'\<close>
    obtain p where S: "set p \<subseteq> set xvec' \<times> set yvec'" and "distinctPerm p" and "yvec' = p \<bullet> xvec'"
      by(drule_tac Suc) auto
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from \<open>x \<sharp> xvec'\<close> \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_list_nil fresh_list_cons fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S \<open>distinctPerm p\<close> \<open>x \<noteq> y\<close> have "distinctPerm((x, y)#p)" by auto
    moreover from \<open>yvec' = p \<bullet> xvec'\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: calc_atm freshChainSimps)
    ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma distinctApend[simp]:
  fixes xvec :: "name list"
  and   yvec :: "name list"

  shows "(set xvec \<inter> set yvec = {}) = xvec \<sharp>* yvec"
by(auto simp add: fresh_star_def name_list_supp fresh_def)

lemma lengthAux:
  fixes xvec :: "name list"
  and   y    :: name
  and   yvec :: "name list"

  assumes "length xvec = length(y#yvec)"

  obtains z zvec where "xvec = z#zvec" and "length zvec = length yvec"
using assms
by(induct xvec arbitrary: yvec y) auto

lemma lengthAux2:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes "length xvec = length(yvec@y#zvec)"

  obtains xvec1 x xvec2 where "xvec=xvec1@x#xvec2" and "length xvec1 = length yvec" and "length xvec2 = length zvec"
proof -
  assume "\<And>xvec1 x xvec2.
        \<lbrakk>xvec = xvec1 @ x # xvec2; length xvec1 = length yvec;
         length xvec2 = length zvec\<rbrakk>
        \<Longrightarrow> thesis"
  moreover from assms have "\<exists>xvec1 x xvec2. xvec=xvec1@x#xvec2 \<and> length xvec1 = length yvec \<and> length xvec2 = length zvec"
    apply(rule_tac x="take (length yvec) xvec" in exI)
    apply(rule_tac x="hd(drop (length yvec) xvec)" in exI)
    apply(rule_tac x="tl(drop (length yvec) xvec)" in exI)
    by auto
  ultimately show ?thesis by blast
qed

lemma semanticsCases[consumes 11, case_names cInput cCase cPar1 cPar2 cComm1 cComm2 cScope cBang]:
  fixes \<Psi>  :: 'b
  and   cP  :: "('a, 'b, 'c) psi"
  and   cRs :: "('a, 'b, 'c) residual"
  and   C   :: "'d::fs_name"
  and   x1   :: name
  and   x2   :: name
  and   xvec1 :: "name list"
  and   xvec2 :: "name list"
  and   xvec3 :: "name list"
  and   xvec4 :: "name list"
  and   xvec5 :: "name list"

  assumes "\<Psi> \<rhd> cP \<longmapsto>cRs"
  and     "length xvec1 = inputLength cP" and "distinct xvec1"
  and     "length xvec2 = residualLength cRs" and "distinct xvec2"
  and     "length xvec3 = residualLength cRs" and "distinct xvec3"
  and     "length xvec4 = residualLength cRs" and "distinct xvec4"
  and     "length xvec5 = residualLength cRs" and "distinct xvec5"
  and     rInput: "\<And>M K N Tvec P. (\<lbrakk>xvec1 \<sharp>* \<Psi>; xvec1 \<sharp>* cP; xvec1 \<sharp>* cRs\<rbrakk> \<Longrightarrow> cP = M\<lparr>\<lambda>*xvec1 N\<rparr>.P \<and>  cRs = K\<lparr>(N[xvec1::=Tvec])\<rparr> \<prec> P[xvec1::=Tvec] \<and>
                                            \<Psi> \<turnstile> M \<leftrightarrow> K \<and> distinct xvec1 \<and> set xvec1 \<subseteq> supp N \<and> length xvec1=length Tvec \<and>
                                            xvec1 \<sharp>* Tvec \<and> xvec1 \<sharp>* \<Psi> \<and> xvec1 \<sharp>* M \<and> xvec1 \<sharp>* K) \<Longrightarrow> Prop"
  and     rOutput: "\<And>M K N P. \<lbrakk>cP = M\<langle>N\<rangle>.P; cRs = K\<langle>N\<rangle> \<prec> P; \<Psi> \<turnstile> M \<leftrightarrow> K\<rbrakk> \<Longrightarrow> Prop"
  and     rCase: "\<And>Cs P \<phi>. \<lbrakk>cP = Cases Cs; \<Psi> \<rhd> P \<longmapsto> cRs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"
  and     rPar1: "\<And>\<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q. (\<lbrakk>xvec2 \<sharp>* \<Psi>; xvec2 \<sharp>* cP; xvec2 \<sharp>* cRs\<rbrakk> \<Longrightarrow> 
                                         cP = P \<parallel> Q \<and> cRs = \<alpha> \<prec> (P' \<parallel> Q) \<and> xvec2 = bn \<alpha> \<and>
                                          \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle> \<and> distinct A\<^sub>Q \<and>
                                          A\<^sub>Q \<sharp>* P \<and> A\<^sub>Q \<sharp>* Q \<and> A\<^sub>Q \<sharp>* \<Psi> \<and> A\<^sub>Q \<sharp>* \<alpha> \<and> A\<^sub>Q \<sharp>* P' \<and> A\<^sub>Q \<sharp>* C) \<Longrightarrow> Prop"
  and     rPar2: "\<And>\<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P. (\<lbrakk>xvec3 \<sharp>* \<Psi>; xvec3 \<sharp>* cP; xvec3 \<sharp>* cRs\<rbrakk> \<Longrightarrow> 
                                         cP = P \<parallel> Q \<and> cRs = \<alpha> \<prec> (P \<parallel> Q') \<and> xvec3 = bn \<alpha> \<and>
                                          \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q' \<and> extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<and> distinct A\<^sub>P \<and>
                                          A\<^sub>P \<sharp>* P \<and> A\<^sub>P \<sharp>* Q \<and> A\<^sub>P \<sharp>* \<Psi> \<and> A\<^sub>P \<sharp>* \<alpha> \<and> A\<^sub>P \<sharp>* Q' \<and> A\<^sub>P \<sharp>* C) \<Longrightarrow> Prop"
  and     rComm1: "\<And>\<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q.
                   \<lbrakk>cP = P \<parallel> Q; cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop"
  and     rComm2: "\<And>\<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q.
                   \<lbrakk>cP = P \<parallel> Q; cRs = \<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>P' \<parallel> Q';
                    \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto> K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                    \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N;
                    A\<^sub>P \<sharp>* P'; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P \<sharp>* xvec; A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P;
                    A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* K; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* xvec;
                    xvec \<sharp>* \<Psi>; xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* \<Psi>\<^sub>Q; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* Q;
                    xvec \<sharp>* K; A\<^sub>P \<sharp>* C; A\<^sub>Q \<sharp>* C; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop"
  and    rOpen:  "\<And>P  M xvec y yvec N P'. 
                   (\<lbrakk>xvec4 \<sharp>* \<Psi>; xvec4 \<sharp>* cP; xvec4 \<sharp>* cRs; x1 \<sharp> \<Psi>; x1 \<sharp> cP; x1 \<sharp> cRs; x1 \<sharp> xvec4\<rbrakk> \<Longrightarrow>
                    cP = \<lparr>\<nu>x1\<rparr>P \<and> cRs = M\<lparr>\<nu>*(xvec@x1#yvec)\<rparr>\<langle>N\<rangle> \<prec> P' \<and> xvec4=xvec@y#yvec \<and>
                    \<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P' \<and> x1 \<in> supp N \<and> x1 \<sharp> xvec \<and> x1 \<sharp> yvec \<and>
                    distinct xvec \<and> distinct yvec \<and> xvec \<sharp>* \<Psi> \<and> xvec \<sharp>* P \<and> xvec \<sharp>* M \<and> xvec \<sharp>* yvec \<and>
                    yvec \<sharp>* \<Psi> \<and> yvec \<sharp>* P \<and> yvec \<sharp>* M) \<Longrightarrow> Prop"
  and     rScope: "\<And>P \<alpha> P'. (\<lbrakk>xvec5 \<sharp>* \<Psi>; xvec5 \<sharp>* cP; xvec5 \<sharp>* cRs; x2 \<sharp> \<Psi>; x2 \<sharp> cP; x2 \<sharp> cRs; x2 \<sharp> xvec5\<rbrakk> \<Longrightarrow> 
                              cP = \<lparr>\<nu>x2\<rparr>P \<and> cRs = \<alpha> \<prec> \<lparr>\<nu>x2\<rparr>P' \<and>  xvec5 = bn \<alpha> \<and>
                              \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P' \<and> x2 \<sharp> \<Psi> \<and> x2 \<sharp> \<alpha> \<and> bn \<alpha> \<sharp>* subject \<alpha> \<and> distinct(bn \<alpha>)) \<Longrightarrow> Prop"
  and    rBang:  "\<And>P. \<lbrakk>cP = !P; \<Psi> \<rhd> P \<parallel> !P \<longmapsto> cRs; guarded P\<rbrakk> \<Longrightarrow> Prop"
  shows Prop
using \<open>\<Psi> \<rhd> cP \<longmapsto>cRs\<close>
proof(cases rule: semanticsCasesAux[where C="(xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)"])
  case(cInput M K xvec N Tvec P)
  have B: "cP = M\<lparr>\<lambda>*xvec N\<rparr>.P" and C: "cRs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (P[xvec::=Tvec])" 
    by fact+
  from \<open>xvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "xvec \<sharp>* xvec1" by simp
  
  from \<open>length xvec1 = inputLength cP\<close> B have "length xvec1 = length xvec"
    by simp
  then obtain p where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinctPerm p" and "xvec1 = p \<bullet> xvec"
    using \<open>xvec \<sharp>* xvec1\<close> \<open>distinct xvec\<close> \<open>distinct xvec1\<close>
    by(rule_tac constructPerm[where xvec=xvec and yvec=xvec1]) auto
  show ?thesis
  proof(rule rInput[where M=M and K=K and N = "p \<bullet> N" and Tvec=Tvec and P="p \<bullet> P"], goal_cases)
    case 1
    from B \<open>xvec \<sharp>* xvec1\<close> \<open>xvec1 \<sharp>* cP\<close> have "xvec1 \<sharp>* N" and "xvec1 \<sharp>* P"
      by(auto simp add: fresh_star_def inputChainFresh name_list_supp) (auto simp add: fresh_def)

    from \<open>cP = M\<lparr>\<lambda>*xvec N\<rparr>.P\<close> S \<open>xvec1 \<sharp>* N\<close> \<open>xvec1 \<sharp>* P\<close> \<open>xvec1 = p \<bullet> xvec\<close>
    have "cP = M\<lparr>\<lambda>*xvec1 (p \<bullet> N)\<rparr>.(p \<bullet> P)"
      apply simp
      by(subst inputChainAlpha) auto
    moreover from \<open>cRs = K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]\<close> S \<open>xvec1 \<sharp>* N\<close> \<open>xvec1 \<sharp>* P\<close> \<open>xvec1 = p \<bullet> xvec\<close> \<open>length xvec = length Tvec\<close> \<open>distinctPerm p\<close>
    have "cRs =  K\<lparr>((p \<bullet> N)[xvec1::=Tvec])\<rparr> \<prec> (p \<bullet> P)[xvec1::=Tvec]"
      by(simp add: renaming substTerm.renaming)
    moreover note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close>
    moreover from \<open>distinct xvec\<close> \<open>xvec1 = p \<bullet> xvec\<close> have "distinct xvec1" by simp
    moreover from \<open>set xvec \<subseteq> supp N\<close> have "(p \<bullet> set xvec) \<subseteq> (p \<bullet> (supp N))"
      by(simp add: eqvts)
    with \<open>xvec1 = p \<bullet> xvec\<close> have "set xvec1 \<subseteq> supp(p \<bullet> N)" by(simp add: eqvts)
    moreover from \<open>length xvec = length Tvec\<close> \<open>xvec1 = p \<bullet> xvec\<close> have "length xvec1 = length Tvec"
      by simp

    moreover from \<open>xvec1 \<sharp>* cRs\<close> C \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close>
    have "(set xvec1) \<sharp>* Tvec"
      by(rule_tac substTerm.subst3Chain[where T=N]) auto
    hence "xvec1 \<sharp>* Tvec" by simp
    moreover from \<open>xvec \<sharp>* Tvec\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> Tvec)" by(simp add: fresh_star_bij)
    with S \<open>xvec \<sharp>* Tvec\<close> \<open>xvec1 \<sharp>* Tvec\<close> \<open>xvec1 = p \<bullet> xvec\<close> have "xvec1 \<sharp>* Tvec" by simp
    moreover from \<open>xvec \<sharp>* M\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" by(simp add: fresh_star_bij)
    with S \<open>xvec \<sharp>* M\<close> \<open>xvec1 \<sharp>* cP\<close> B \<open>xvec1 = p \<bullet> xvec\<close> have "xvec1 \<sharp>* M" by simp
    moreover from \<open>xvec \<sharp>* K\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> K)" by(simp add: fresh_star_bij)
    with S \<open>xvec \<sharp>* K\<close> \<open>xvec1 \<sharp>* cRs\<close> C \<open>xvec1 = p \<bullet> xvec\<close> have "xvec1 \<sharp>* K" by simp
    ultimately show ?case using \<open>xvec1 \<sharp>* \<Psi>\<close> by blast 
  qed
next
  case(cOutput M K N P)
  thus ?thesis by(rule rOutput) 
next
  case(cCase Cs P \<phi>)
  thus ?thesis by(rule rCase) 
next
  case(cPar1 \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q)
  have B: "cP = P \<parallel> Q" and C: "cRs = \<alpha> \<prec> P' \<parallel> Q"
    by fact+
  from \<open>bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "bn \<alpha> \<sharp>* xvec2" by simp
  from \<open>A\<^sub>Q \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "A\<^sub>Q \<sharp>* xvec2" and "A\<^sub>Q \<sharp>* C" by simp+
  
  from \<open>length xvec2 = residualLength cRs\<close> C have "length xvec2 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "xvec2= bn(p \<bullet> \<alpha>)"
    using \<open>bn \<alpha> \<sharp>* xvec2\<close> \<open>distinct(bn \<alpha>)\<close> \<open>distinct xvec2\<close>
    by(rule_tac constructPerm[where xvec="bn \<alpha>" and yvec=xvec2]) (auto simp add: eqvts)
  show ?thesis
  proof(rule rPar1[where P=P and Q=Q and \<alpha>="p \<bullet> \<alpha>" and P'="p \<bullet> P'" and A\<^sub>Q=A\<^sub>Q and \<Psi>\<^sub>Q=\<Psi>\<^sub>Q], goal_cases)
    case 1
    note \<open>cP = P \<parallel> Q\<close>
    moreover from B C S \<open>bn \<alpha> \<sharp>* xvec2\<close> \<open>xvec2 \<sharp>* cRs\<close> \<open>xvec2 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec2 \<sharp>* cP\<close> \<open>bn \<alpha> \<sharp>* Q\<close>
    have "cRs = (p \<bullet> \<alpha>) \<prec> (p \<bullet> P') \<parallel> Q"
      apply auto
      by(subst residualAlpha[where p=p]) auto
    moreover note \<open>xvec2 = bn(p \<bullet> \<alpha>)\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> S B C S \<open>bn \<alpha> \<sharp>* xvec2\<close> \<open>xvec2 \<sharp>* cRs\<close> \<open>xvec2 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec2 \<sharp>* cP\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
      by(subst residualAlpha[symmetric]) auto
    moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
    moreover from \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* xvec2\<close> S \<open>xvec2 = bn(p \<bullet> \<alpha>)\<close> \<open>distinctPerm p\<close> have "A\<^sub>Q \<sharp>* (p \<bullet> \<alpha>)"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover from \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* xvec2\<close> S \<open>xvec2 = bn(p \<bullet> \<alpha>)\<close> \<open>distinctPerm p\<close> have "A\<^sub>Q \<sharp>* (p \<bullet> P')"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover note \<open>A\<^sub>Q \<sharp>* C\<close>
    ultimately show ?case by blast
  qed
next
  case(cPar2 \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P)
  have B: "cP = P \<parallel> Q" and C: "cRs = \<alpha> \<prec> P \<parallel> Q'"
    by fact+
  from \<open>bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "bn \<alpha> \<sharp>* xvec3" by simp
  from \<open>A\<^sub>P \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "A\<^sub>P \<sharp>* xvec3" and "A\<^sub>P \<sharp>* C" by simp+
  
  from \<open>length xvec3 = residualLength cRs\<close> C have "length xvec3 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "xvec3 = bn(p \<bullet> \<alpha>)"
    using \<open>bn \<alpha> \<sharp>* xvec3\<close> \<open>distinct(bn \<alpha>)\<close> \<open>distinct xvec3\<close>
    by(rule_tac constructPerm[where xvec="bn \<alpha>" and yvec=xvec3]) (auto simp add: eqvts)
  show ?thesis
  proof(rule rPar2[where P=P and Q=Q and \<alpha>="p \<bullet> \<alpha>" and Q'="p \<bullet> Q'" and A\<^sub>P=A\<^sub>P and \<Psi>\<^sub>P=\<Psi>\<^sub>P], goal_cases)
    case 1
    note \<open>cP = P \<parallel> Q\<close>
    moreover from B C S \<open>bn \<alpha> \<sharp>* xvec3\<close> \<open>xvec3 \<sharp>* cRs\<close> \<open>xvec3 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec3 \<sharp>* cP\<close> \<open>bn \<alpha> \<sharp>* P\<close>
    have "cRs = (p \<bullet> \<alpha>) \<prec> P \<parallel> (p \<bullet> Q')"
      apply auto
      by(subst residualAlpha[where p=p]) auto
    moreover note \<open>xvec3 = bn(p \<bullet> \<alpha>)\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> S B C S \<open>bn \<alpha> \<sharp>* xvec3\<close> \<open>xvec3 \<sharp>* cRs\<close> \<open>xvec3 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec3 \<sharp>* cP\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> Q')"
      by(subst residualAlpha[symmetric]) auto
    moreover note \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
    moreover from \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* xvec3\<close> S \<open>xvec3 = bn(p \<bullet> \<alpha>)\<close> \<open>distinctPerm p\<close> have "A\<^sub>P \<sharp>* (p \<bullet> \<alpha>)"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover from \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* xvec3\<close> S \<open>xvec3 = bn(p \<bullet> \<alpha>)\<close> \<open>distinctPerm p\<close> have "A\<^sub>P \<sharp>* (p \<bullet> Q')"
      by(subst fresh_star_bij[symmetric, where pi=p]) simp
    moreover note \<open>A\<^sub>P \<sharp>* C\<close>
    ultimately show ?case by blast
  qed
next
  case(cComm1 \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q)
  thus ?thesis by(rule_tac rComm1[where P=P and Q=Q]) (assumption | simp)+
next
  case(cComm2 \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q)
  thus ?thesis by(rule_tac rComm2[where P=P and Q=Q]) (assumption | simp)+
next
  case(cOpen P M xvec yvec N P' x)
  have B: "cP = \<lparr>\<nu>x\<rparr>P" and C: "cRs = M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by fact+
  from \<open>xvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "xvec \<sharp>* xvec4" and "xvec \<sharp>* cP" and "xvec \<sharp>* cRs" and "x1 \<sharp> xvec" by simp+
  from \<open>x \<sharp> (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "x \<sharp> xvec4" and "x \<sharp> cP" and "x \<sharp> cRs" and "x \<noteq> x1" by simp+
  from \<open>yvec \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "yvec \<sharp>* xvec4" and "yvec \<sharp>* cP"  and "yvec \<sharp>* cRs" and "x1 \<sharp> yvec" by simp+

  from \<open>xvec \<sharp>* cRs\<close> \<open>x \<sharp> cRs\<close> \<open>yvec \<sharp>* cRs\<close> C have "(xvec@x#yvec) \<sharp>* M" by simp
  from \<open>xvec \<sharp>* \<Psi>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(xvec@x#yvec) \<sharp>* \<Psi>" by simp
  from \<open>length xvec4 = residualLength cRs\<close> C obtain xvec' y yvec' where D: "xvec4 = xvec'@y#yvec'" and "length xvec' = length xvec" and "length yvec' = length yvec"
    by(rule_tac lengthAux2) auto
  with \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* xvec4\<close> \<open>yvec \<sharp>* xvec4\<close> \<open>x \<sharp> xvec4\<close> \<open>distinct xvec4\<close>
  have "distinct xvec'" and "distinct yvec'" and "xvec' \<sharp>* yvec'" and "x \<noteq> y" and "y \<sharp> xvec'" and "y \<sharp> yvec'" 
   and "x \<sharp> xvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec" and "y \<sharp> yvec" and "xvec \<sharp>* xvec'" and "yvec \<sharp>* yvec'"
    by auto
  from \<open>length xvec' = length xvec\<close> \<open>xvec \<sharp>* xvec'\<close> \<open>distinct xvec\<close> \<open>distinct xvec'\<close> 
  obtain p where Sp: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinctPerm p" and E: "xvec' = p \<bullet> xvec"
    by(metis constructPerm)
  from \<open>length yvec' = length yvec\<close> \<open>yvec \<sharp>* yvec'\<close> \<open>distinct yvec\<close> \<open>distinct yvec'\<close> 
  obtain q where Sq: "set q \<subseteq> set yvec \<times> set(q \<bullet> yvec)" and "distinctPerm q" and F: "yvec' = q \<bullet> yvec"
    by(metis constructPerm)

  show ?thesis
  proof(rule rOpen[where P="([(x, x1)] \<bullet> P)" and xvec="p \<bullet> xvec" and y="y" and yvec="q \<bullet> yvec" and N="(p@(x1, x)#q) \<bullet> N" and P'="(p@(x1, x)#q) \<bullet> P'" and M=M], goal_cases)
    case 1
    from \<open>xvec \<sharp>* xvec4\<close> \<open>x \<sharp> xvec4\<close> \<open>x1 \<sharp> xvec4\<close> \<open>yvec \<sharp>* xvec4\<close> D E F
    have "x \<noteq> y" and "x1 \<noteq> y" and "x1 \<sharp> p \<bullet> xvec" and "x1 \<sharp> q \<bullet> yvec" by simp+
    from \<open>xvec4 \<sharp>* cRs\<close> \<open>x1 \<sharp> cRs\<close> C have "xvec4 \<sharp>* M" and "x1 \<sharp> M" by simp+
    from \<open>cP = \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<sharp> cP\<close> \<open>x \<noteq> x1\<close> have "([(x, x1)] \<bullet> cP) = [(x, x1)] \<bullet> \<lparr>\<nu>x\<rparr>P"
      by simp
    with \<open>x \<sharp> cP\<close> \<open>x1 \<sharp> cP\<close> have "cP = \<lparr>\<nu>x1\<rparr>([(x, x1)] \<bullet> P)" by(simp add: eqvts calc_atm)
    moreover from C have "((p@(x1, x)#q) \<bullet> cRs) = (p@(x1, x)#q) \<bullet> (M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P')" by(simp add: fresh_star_bij)
    with Sp Sq \<open>xvec4 \<sharp>* cRs\<close> D E F \<open>xvec \<sharp>* cRs\<close> \<open>x \<sharp> cRs\<close> \<open>yvec \<sharp>* cRs\<close> \<open>xvec4 \<sharp>* M\<close> \<open>(xvec@x#yvec) \<sharp>* M\<close> \<open>xvec \<sharp>* xvec4\<close> \<open>x \<sharp> xvec4\<close> \<open>yvec \<sharp>* xvec4\<close> \<open>xvec \<sharp>* yvec\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> \<open>xvec' \<sharp>* yvec'\<close> \<open>x1 \<sharp> xvec\<close> \<open>x1 \<sharp> yvec\<close> \<open>x1 \<noteq> y\<close> \<open>x1 \<sharp> xvec4\<close> \<open>x1 \<sharp> cRs\<close> \<open>x1 \<sharp> cRs\<close> \<open>x \<noteq> x1\<close> \<open>x1 \<sharp> M\<close>
    have "cRs = M\<lparr>\<nu>*((p \<bullet> xvec)@x1#(q \<bullet> yvec))\<rparr>\<langle>((p@(x1, x)#q) \<bullet> N)\<rangle> \<prec> ((p@(x1, x)#q) \<bullet> P')"
      by(simp add: eqvts pt2[OF pt_name_inst] calc_atm)
    moreover from D E F have "xvec4 = (p \<bullet> xvec)@y#(q \<bullet> yvec)" by simp
    moreover from \<open>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "((p@(x1, x)#q) \<bullet> \<Psi>) \<rhd> ((p@(x1, x)#q) \<bullet> P) \<longmapsto>((p@(x1, x)#q) \<bullet> (M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'))"
      by(intro eqvts)
    with Sp Sq B C D E F \<open>xvec4 \<sharp>* \<Psi>\<close> \<open>(xvec@x#yvec) \<sharp>* \<Psi>\<close> \<open>xvec4 \<sharp>* cRs\<close> \<open>x \<sharp> xvec4\<close> C D \<open>x \<sharp> cRs\<close> \<open>yvec \<sharp>* cRs\<close> \<open>xvec4 \<sharp>* M\<close> \<open>(xvec@x#yvec) \<sharp>* M\<close> \<open>x \<sharp> M\<close> \<open>x1 \<sharp> cRs\<close> \<open>x \<noteq> x1\<close> \<open>x1 \<sharp> xvec\<close> \<open>x1 \<sharp> yvec\<close> \<open>xvec \<sharp>* xvec4\<close> \<open>yvec \<sharp>* xvec4\<close> \<open>x1 \<sharp> xvec4\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x1 \<sharp> \<Psi>\<close> \<open>xvec4 \<sharp>* cP\<close> \<open>xvec \<sharp>* P\<close> \<open>yvec \<sharp>* P\<close> \<open>xvec' \<sharp>* yvec'\<close> \<open>x1 \<sharp> xvec4\<close> \<open>xvec4 \<sharp>* cP\<close> \<open>yvec \<sharp>* xvec4\<close> \<open>xvec \<sharp>* xvec4\<close> \<open>x \<noteq> x1\<close> \<open>xvec \<sharp>* yvec\<close>
    have "\<Psi> \<rhd> ([(x, x1)] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*((p \<bullet> xvec)@(q \<bullet> yvec))\<rparr>\<langle>((p@(x1, x)#q) \<bullet> N)\<rangle> \<prec> ((p@(x1, x)#q) \<bullet> P')" 
      by(simp add: eqvts  pt_fresh_bij[OF pt_name_inst, OF at_name_inst] pt2[OF pt_name_inst] name_swap)
    
    moreover from \<open>x \<in> supp N\<close> have "((p@(x1, x)#q) \<bullet> x) \<in> ((p@(x1, x)#q) \<bullet> supp N)"
      by(simp add: pt_set_bij[OF pt_name_inst, OF at_name_inst])
    hence "x1 \<in> supp((p@(x1, x)#q) \<bullet> N)"
      using \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x1 \<sharp> xvec\<close> \<open>x1 \<sharp> yvec\<close> \<open>x \<sharp> xvec4\<close> \<open>x1 \<sharp> xvec4\<close> \<open>xvec \<sharp>* xvec4\<close> \<open>yvec \<sharp>* xvec4\<close> \<open>xvec' \<sharp>* yvec'\<close> D E F Sp Sq \<open>x \<noteq> x1\<close>
      by(simp add: eqvts pt2[OF pt_name_inst] calc_atm)
    moreover from \<open>x1 \<sharp> xvec4\<close> D E F have "x1 \<sharp> (p \<bullet> xvec)" and "x1 \<sharp> (q \<bullet> yvec)" by simp+
    moreover from \<open>distinct xvec'\<close> \<open>distinct yvec'\<close> E F have "distinct(p \<bullet> xvec)" and "distinct(q \<bullet> yvec)" by simp+
    moreover from \<open>xvec' \<sharp>* yvec'\<close> E F have "(p \<bullet> xvec) \<sharp>* (q \<bullet> yvec)" by auto
    moreover from \<open>xvec \<sharp>* \<Psi>\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with Sp D E \<open>xvec4 \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<close> have "(p \<bullet> xvec) \<sharp>* \<Psi>" by(simp add: eqvts)
    moreover from \<open>yvec \<sharp>* \<Psi>\<close> have "(p \<bullet> yvec) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with Sq D F \<open>xvec4 \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* \<Psi>\<close> have "(q \<bullet> yvec) \<sharp>* \<Psi>" by(simp add: eqvts)
    moreover from \<open>xvec4 \<sharp>* cP\<close> \<open>x \<sharp> xvec4\<close> \<open>x1 \<sharp> xvec4\<close> B D E F have "(p \<bullet> xvec) \<sharp>* ([(x, x1)] \<bullet> P)" and "(q \<bullet> yvec) \<sharp>* ([(x, x1)] \<bullet> P)"
      by simp+
    moreover from \<open>xvec4 \<sharp>* M\<close> C D E F have "(p \<bullet> xvec) \<sharp>* M" and "(q \<bullet> yvec) \<sharp>* M" by simp+
    ultimately show ?case
      by blast
  qed
next
  case(cScope P \<alpha> P' x)
  have B: "cP = \<lparr>\<nu>x\<rparr>P" and C: "cRs = \<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
    by fact+
  from \<open>bn \<alpha> \<sharp>* (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "bn \<alpha> \<sharp>* xvec5" and "x2 \<sharp> bn \<alpha>" by simp+
  from \<open>x \<sharp> (xvec1, xvec2, xvec3, xvec4, xvec5, x1, x2, cP, cRs, C)\<close> have "x \<sharp> xvec5" and "x \<noteq> x2" and "x \<sharp> cRs" by simp+
  
  from \<open>length xvec5 = residualLength cRs\<close> C have "length xvec5 = length(bn \<alpha>)"
    by simp
  then obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "xvec5= bn(p \<bullet> \<alpha>)"
    using \<open>bn \<alpha> \<sharp>* xvec5\<close> \<open>distinct(bn \<alpha>)\<close> \<open>distinct xvec5\<close>
    by(rule_tac constructPerm[where xvec="bn \<alpha>" and yvec=xvec5]) (auto simp add: eqvts)
  show ?thesis
  proof(rule rScope[where P="[(x, x2)] \<bullet> P" and \<alpha>="[(x, x2)] \<bullet> p \<bullet> \<alpha>" and P'="[(x, x2)] \<bullet> p \<bullet> P'"], goal_cases)
    case 1
    from \<open>x2 \<sharp> cRs\<close> C \<open>x2 \<sharp> bn \<alpha>\<close> \<open>x \<noteq> x2\<close> have "x2 \<sharp> \<alpha>" and "x2 \<sharp> P'" by(auto simp add: abs_fresh)
    from \<open>cP = \<lparr>\<nu>x\<rparr>P\<close> \<open>x2 \<sharp> cP\<close> \<open>x \<noteq> x2\<close> have "cP = \<lparr>\<nu>x2\<rparr>([(x, x2)] \<bullet> P)"
      by(simp add: alphaRes abs_fresh)
    moreover from B C S \<open>bn \<alpha> \<sharp>* xvec5\<close> \<open>xvec5 \<sharp>* cRs\<close> \<open>xvec5 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec5 \<sharp>* cP\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> xvec5\<close> 
    have "cRs = (p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P')"
      apply auto
      by(subst residualAlpha[where p=p] alphaRes) (auto simp del: actionFresh)
    hence "([(x, x2)] \<bullet> cRs) = [(x, x2)] \<bullet> ((p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x\<rparr>(p \<bullet> P'))"
      by simp
    with \<open>x2 \<sharp> cRs\<close> \<open>x \<sharp> cRs\<close> have "cRs = ([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<prec> \<lparr>\<nu>x2\<rparr>([(x, x2)] \<bullet> p \<bullet> P')"
      by(simp add: eqvts calc_atm)
    moreover from \<open>xvec5= bn(p \<bullet> \<alpha>)\<close> have "([(x, x2)] \<bullet> xvec5) = ([(x, x2)] \<bullet> bn(p \<bullet> \<alpha>))"
      by simp
    with \<open>x \<sharp> xvec5\<close> \<open>x2 \<sharp> xvec5\<close> have "xvec5 = bn([(x, x2)] \<bullet> p \<bullet> \<alpha>)"
      by(simp add: eqvts)
    moreover from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> S B C S \<open>bn \<alpha> \<sharp>* xvec5\<close> \<open>xvec5 \<sharp>* cRs\<close> \<open>xvec5 = bn(p \<bullet> \<alpha>)\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>xvec5 \<sharp>* cP\<close> \<open>x \<sharp> xvec5\<close>
    have "\<Psi> \<rhd> P \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
      by(subst residualAlpha[symmetric]) auto
    hence "([(x, x2)] \<bullet> \<Psi>) \<rhd> ([(x, x2)] \<bullet> P) \<longmapsto>([(x, x2)] \<bullet> ((p \<bullet> \<alpha>) \<prec> (p \<bullet> P')))"
      by(rule eqvt)
    with \<open>x \<sharp> \<Psi>\<close> \<open>x2 \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> ([(x, x2)] \<bullet> P) \<longmapsto>([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<prec> ([(x, x2)] \<bullet> p \<bullet> P')"
      by(simp add: eqvts)
    moreover note \<open>x2 \<sharp> \<Psi>\<close>
    moreover from \<open>x \<sharp> \<alpha>\<close> \<open>x2 \<sharp> \<alpha>\<close> \<open>x \<sharp> xvec5\<close> \<open>x2 \<sharp> xvec5\<close> S \<open>x \<noteq> x2\<close> \<open>xvec5 = bn(p \<bullet> \<alpha>)\<close> have "x2 \<sharp> [(x, x2)] \<bullet> p \<bullet> \<alpha>"
      apply(subgoal_tac "x \<sharp> p \<and> x2 \<sharp> p")
      apply(simp add: perm_compose freshChainSimps del: actionFresh)
      by(auto dest: freshAlphaSwap)
    moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "([(x, x2)] \<bullet> p \<bullet> (bn \<alpha>)) \<sharp>* ([(x, x2)] \<bullet> p \<bullet> (subject \<alpha>))"
      by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    hence "bn([(x, x2)] \<bullet> p \<bullet> \<alpha>) \<sharp>* subject([(x, x2)] \<bullet> p \<bullet> \<alpha>)"
      by(simp add: eqvts)
    moreover from \<open>distinct(bn \<alpha>)\<close> have "distinct([(x, x2)] \<bullet> p \<bullet> (bn \<alpha>))" by simp
    hence "distinct(bn([(x, x2)] \<bullet> p \<bullet> \<alpha>))" by(simp add: eqvts)
    ultimately show ?case  by blast
  qed
next
  case(cBang P)
  thus ?thesis by(rule_tac rBang) auto
qed

lemma parCases[consumes 5, case_names cPar1 cPar2 cComm1 cComm2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> T"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P';  extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                                  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* P'; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q';  extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                                 A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P \<parallel> Q')"
  and     rComm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K; xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rComm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K;  xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"

  shows "Prop \<alpha> T"
proof -
  from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
  have "length(bn \<alpha>) = residualLength(\<alpha> \<prec> T)" by simp
  note Trans
  moreover have "length [] = inputLength(P \<parallel> Q)" and "distinct []"
    by(auto simp add: inputLength_inputLength'_inputLength''.simps)
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> T)\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> T)\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> T)\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> T)\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> \<alpha>" and "x \<sharp> T"
    by(generate_fresh "name") auto
  ultimately show ?thesis using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
    apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ C x x])
    apply(auto simp add: psi.inject)
    apply(force simp add: residualInject residualInject' intro: rPar1)
    apply(force simp add: residualInject residualInject' intro: rPar2)
    apply(fastforce simp add: residualInject residualInject' intro: rComm1)
    by(fastforce simp add: residualInject residualInject' intro: rComm2)
qed

lemma parInputCases[consumes 1, case_names cPar1 cPar2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a
  and   R :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> R"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P';  extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop R"
proof -
  from Trans obtain \<alpha> where "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> R" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* subject \<alpha>" and "\<alpha> = M\<lparr>N\<rparr>" by auto
  thus ?thesis using rPar1 rPar2
    by(induct rule: parCases) (auto simp add: residualInject)
qed

lemma parOutputCases[consumes 5, case_names cPar1 cPar2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   xvec :: "name list"
  and   N :: 'a
  and   R :: "('a, 'b, 'c) psi"
  and   C :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R"
  and            "xvec \<sharp>* \<Psi>"
  and            "xvec \<sharp>* P"
  and            "xvec \<sharp>* Q"
  and            "xvec \<sharp>* M"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P';  extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* xvec; A\<^sub>Q \<sharp>* N; A\<^sub>Q \<sharp>* C; A\<^sub>Q \<sharp>* xvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* xvec; A\<^sub>P \<sharp>* N; A\<^sub>P \<sharp>* C; A\<^sub>P \<sharp>* xvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop R"
proof -
  from Trans have "distinct xvec" by(auto dest: boundOutputDistinct)
  obtain \<alpha> where "\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>" by simp
  with Trans \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close>
  have "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> R" and "bn \<alpha> \<sharp>* \<Psi>" and "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" "bn \<alpha> \<sharp>* subject \<alpha>"
    by simp+
  thus ?thesis using \<open>\<alpha>=M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>\<close> rPar1 rPar2 \<open>distinct xvec\<close>
    by(induct rule: parCases[where C="(xvec, C)"]) (auto simp add: residualInject)
qed

lemma theEqvt[eqvt_force]:
  fixes p :: "name prm"
  and   \<alpha> :: "'a action"

  assumes "\<alpha> \<noteq> \<tau>"

  shows "(p \<bullet> the(subject \<alpha>)) = the(p \<bullet> (subject \<alpha>))"
using assms
by(induct rule: actionCases[where \<alpha>=\<alpha>]) auto

lemma theSubjectFresh[simp]:
  fixes \<alpha> :: "'a action"
  and   x :: name

  assumes "\<alpha> \<noteq> \<tau>"

  shows "x \<sharp> the(subject \<alpha>) = x \<sharp> subject \<alpha>"
using assms
by(cases rule: actionCases) auto

lemma theSubjectFreshChain[simp]:
  fixes \<alpha>    :: "'a action"
  and   xvec :: "name list"

  assumes "\<alpha> \<noteq> \<tau>"

  shows "xvec \<sharp>* the(subject \<alpha>) = xvec \<sharp>* subject \<alpha>"
using assms
by(cases rule: actionCases) auto

lemma obtainPrefix:
  fixes \<Psi> :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'  :: "('a, 'b, 'c) psi"
  and   A\<^sub>P  :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   B   :: "name list"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "\<alpha> \<noteq> \<tau>"
  and     "B \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* B"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* subject \<alpha>"

  obtains M where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
using assms
proof(nominal_induct avoiding: B arbitrary: thesis rule: semanticsFrameInduct')
  case(cAlpha \<Psi> P \<alpha> P' p A\<^sub>P \<Psi>\<^sub>P B)
  then obtain M where subjEq: "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
    by(rule_tac cAlpha) auto
  from \<open>set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> subjEq
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject(p \<bullet> \<alpha>)) \<leftrightarrow> M"
    by(simp add: subjectEqvt[symmetric])
  thus ?case using cAlpha \<open>B \<sharp>* M\<close>
    by auto
next
  case(cFrameAlpha \<Psi> P A\<^sub>P \<Psi>\<^sub>P p \<alpha> P' B)
  then obtain M where subjEq: "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M" 
    by(rule_tac cFrameAlpha) auto
  have S: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)" by fact
  from subjEq have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<turnstile> (p \<bullet> the(subject \<alpha>)) \<leftrightarrow> (p \<bullet> M)"
    by(rule chanEqClosed)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* subject \<alpha>\<close> S \<open>\<alpha> \<noteq> \<tau>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
  have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> the(subject \<alpha>) \<leftrightarrow> (p \<bullet> M)"
    by(simp add: eqvts del: subjectEqvt)
  moreover from \<open>B \<sharp>* M\<close> have "(p \<bullet> B) \<sharp>* (p \<bullet> M)"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  with \<open>A\<^sub>P \<sharp>* B\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* B\<close> S have "B \<sharp>* (p \<bullet> M)" by(simp add: eqvts)
  ultimately show ?case by(rule cFrameAlpha)
next
  case(cInput \<Psi> M K xvec N Tvec P B)
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt AssertionStatEqSym[OF Identity])
  hence "\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> M" by(rule chanEqSym)
  moreover from \<open>B \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)\<close> have "B \<sharp>* M" by simp
  ultimately show ?case by(rule_tac cInput) auto
next
  case(cOutput \<Psi> M K N P B)
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt AssertionStatEqSym[OF Identity])
  hence "\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> M"
    by(rule chanEqSym)
  moreover from \<open>B \<sharp>* (M\<langle>N\<rangle>.P)\<close> have "B \<sharp>* M" by simp
  ultimately show ?case by(rule_tac cOutput) auto
next
  case(cCase \<Psi> P \<alpha> P' \<phi> Cs  A\<^sub>P \<Psi>\<^sub>P B)
  then obtain M where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
    by(rule_tac cCase) (auto dest: memFreshChain)
  with \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> show ?case by(blast intro: cCase statEqEnt compositionSym Identity)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P B)
  then obtain M where "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
    apply(rule_tac cPar1) by assumption auto
  thus ?case
    by(metis cPar1 statEqEnt Associativity Commutativity AssertionStatEqTrans Composition)
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q B)
  then obtain M where "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
    by(rule_tac cPar2) auto
  thus ?case by(metis cPar2 statEqEnt Associativity)
next
  case cComm1
  thus ?case by simp
next
  case cComm2
  thus ?case by simp
next
  case(cOpen \<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P B)  
  then obtain K where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" and "B \<sharp>* K"
    apply(rule_tac cOpen) by force auto
  thus ?case by(fastforce intro: cOpen)
next
  case(cScope \<Psi> P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P B)  
  then obtain M where "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> the(subject \<alpha>) \<leftrightarrow> M" and "B \<sharp>* M"
    by(rule_tac cScope) auto
  thus ?case by(fastforce intro: cScope)
next
  case(cBang \<Psi> P \<alpha> P' A\<^sub>P \<Psi>\<^sub>P B)
  then obtain K where "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> the(subject \<alpha>) \<leftrightarrow> K" and "B \<sharp>* K"
    by(rule_tac cBang) auto
  with \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> show ?case by(metis cBang statEqEnt compositionSym Identity)
qed

lemma inputRenameSubject:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* K"
    
  shows "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'"
using assms
proof(nominal_induct avoiding: K rule: inputFrameInduct)
  case(cAlpha \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P  p K)
  have S: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)" by fact
  from \<open>\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)" 
    by(rule chanEqClosed)
  with S \<open>distinctPerm p\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* K\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" by(simp add: eqvts)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> 
       \<open>\<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close>
  show ?case by blast
next
  case(cInput \<Psi> M K xvec N Tvec P K')
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> K'\<close> have "\<Psi> \<turnstile> K \<leftrightarrow> K'"
    by(blast intro: statEqEnt Identity)
  with \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<turnstile> M \<leftrightarrow> K'"
    by(rule chanEqTrans)
  thus ?case using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
    by(rule Input)
next
  case(cCase \<Psi> P M N P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity compositionSym AssertionStatEqSym)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close>
    \<open>\<And>K. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close>
  have "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by force
  thus ?case using \<open>(\<phi>, P) mem Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> by(rule Case)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
    by(metis statEqEnt Associativity Composition AssertionStatEqTrans Commutativity)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> 
       \<open>\<And>K. \<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q); A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by force
  thus ?case using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* N\<close>
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q M N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q K)
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    by(rule statEqEnt[OF AssertionStatEqSym[OF Associativity]])
  with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* K\<close> 
       \<open>\<And>K. \<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>Q \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P); A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by force
  thus ?case using \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* N\<close>
    by(rule_tac Par2) auto
next
  case(cScope \<Psi> P M N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by force
  with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> N\<close> show ?case
    by(rule_tac Scope) auto
next
  case(cBang \<Psi> P M N P' A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity compositionSym AssertionStatEqSym)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close>
    \<open>\<And>K. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* (P \<parallel> !P); A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<parallel> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'\<close>
  have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P'" by force
  thus ?case using \<open>guarded P\<close> by(rule Bang)
qed

lemma outputRenameSubject:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>P \<sharp>* K"
    
  shows "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
using assms
apply(simp add: residualInject)
proof(nominal_induct avoiding: K rule: outputFrameInduct)
  case(cAlpha \<Psi> P M A\<^sub>P \<Psi>\<^sub>P p B K)
  have S: "set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P)" by fact
  from \<open>\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P))) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)" 
    by(rule chanEqClosed)
  with S \<open>distinctPerm p\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* M\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* K\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K" by(simp add: eqvts)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> 
  show ?case by(blast intro: cAlpha)
next
  case(cOutput \<Psi> M K N P K')
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> K \<leftrightarrow> K'\<close> have "\<Psi> \<turnstile> K \<leftrightarrow> K'"
    by(blast intro: statEqEnt Identity)
  with \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<turnstile> M \<leftrightarrow> K'"
    by(rule chanEqTrans)
  thus ?case using Output by(force simp add: residualInject)
next
  case(cCase \<Psi> P M B \<phi> Cs A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity compositionSym AssertionStatEqSym)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close>
    \<open>\<And>K. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>(ROut K B)\<close>
  have "\<Psi> \<rhd> P \<longmapsto>ROut K B" by force
  thus ?case using \<open>(\<phi>, P) mem Cs\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> by(rule Case)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K"
    by(metis statEqEnt Associativity Composition AssertionStatEqTrans Commutativity)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close> 
       \<open>\<And>K. \<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q); A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>(ROut K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P'))\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(force simp add: residualInject)
  thus ?case using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* K\<close>  \<open>A\<^sub>Q \<sharp>* xvec\<close>  \<open>A\<^sub>Q \<sharp>* N\<close> Par1[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(auto simp add: residualInject)
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q M xvec N Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q K)
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
    by(rule statEqEnt[OF AssertionStatEqSym[OF Associativity]])
  with \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* K\<close> 
       \<open>\<And>K. \<lbrakk>(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; A\<^sub>Q \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>P); A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; A\<^sub>Q \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>ROut K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q')\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>ROut K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' Q')" by force
  thus ?case using \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* K\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* N\<close> Par2[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"]
    by(auto simp add: residualInject)
next
  case(cOpen \<Psi> P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(force simp add: residualInject)
  with \<open>x \<in> supp N\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> Open show ?case
    by(auto simp add: residualInject)
next
  case(cScope \<Psi> P M xvec N P' x A\<^sub>P \<Psi>\<^sub>P)
  hence "\<Psi> \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(force simp add: residualInject)
  with \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> K\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> N\<close> Scope[where \<alpha>="K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>"] show ?case
    by(auto simp add: residualInject)
next
  case(cBang \<Psi> P M B A\<^sub>P \<Psi>\<^sub>P K)
  from \<open>\<Psi> \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity compositionSym AssertionStatEqSym)
  with \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K\<close>
    \<open>\<And>K. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* (P \<parallel> !P); A\<^sub>P \<sharp>* M; A\<^sub>P \<sharp>* K\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<parallel> !P \<longmapsto>ROut K B\<close>
  have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>ROut K B" by force
  thus ?case using \<open>guarded P\<close> by(rule Bang)
qed

lemma parCasesSubject[consumes 7, case_names cPar1 cPar2 cComm1 cComm2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   R    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"
  and   yvec :: "name list"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>\<alpha> \<prec> R"
  and            "bn \<alpha> \<sharp>* \<Psi>"
  and            "bn \<alpha> \<sharp>* P"
  and            "bn \<alpha> \<sharp>* Q"
  and            "bn \<alpha> \<sharp>* subject \<alpha>"
  and            "yvec \<sharp>* P"
  and            "yvec \<sharp>* Q"
  and     rPar1: "\<And>P' A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P';  extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
                       A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* \<alpha>; A\<^sub>Q \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
                       A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* \<alpha>; A\<^sub>P \<sharp>* C\<rbrakk> \<Longrightarrow> Prop \<alpha> (P \<parallel> Q')"
  and     rComm1: "\<And>\<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; yvec \<sharp>* M; yvec \<sharp>* K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K; xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
  and     rComm2: "\<And>\<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q.
           \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; distinct A\<^sub>P;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; distinct A\<^sub>Q;
            \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K; yvec \<sharp>* M; yvec \<sharp>* K; distinct xvec;
            A\<^sub>P \<sharp>* \<Psi>;  A\<^sub>P \<sharp>* \<Psi>\<^sub>Q;  A\<^sub>P \<sharp>* P;  A\<^sub>P \<sharp>* M;  A\<^sub>P \<sharp>* N;  A\<^sub>P \<sharp>* P';  A\<^sub>P \<sharp>* Q;  A\<^sub>P \<sharp>* xvec;  A\<^sub>P \<sharp>* Q'; A\<^sub>P \<sharp>* A\<^sub>Q;  A\<^sub>P \<sharp>* C; 
            A\<^sub>Q \<sharp>* \<Psi>;  A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>Q \<sharp>* P;  A\<^sub>Q \<sharp>* K;  A\<^sub>Q \<sharp>* N;  A\<^sub>Q \<sharp>* P';  A\<^sub>Q \<sharp>* Q;  A\<^sub>Q \<sharp>* xvec;  A\<^sub>Q \<sharp>* Q'; A\<^sub>Q \<sharp>* C; 
            xvec \<sharp>* \<Psi>;  xvec \<sharp>* \<Psi>\<^sub>P; xvec \<sharp>* P;  xvec \<sharp>* M;  xvec \<sharp>* K;  xvec \<sharp>* Q;  xvec \<sharp>* \<Psi>\<^sub>Q;  xvec \<sharp>* C\<rbrakk> \<Longrightarrow>
            Prop (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"

  shows "Prop \<alpha> R"
using Trans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
proof(induct rule: parCases[where C="(C, yvec)"])
  case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
  thus ?case by(rule_tac rPar1) auto 
next
  case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
  thus ?case by(rule_tac rPar2) auto
next
  case(cComm1 \<Psi>\<^sub>Q M N P' A\<^sub>P \<Psi>\<^sub>P K xvec Q' A\<^sub>Q)
  from \<open>A\<^sub>P \<sharp>* (C, yvec)\<close> \<open>A\<^sub>Q \<sharp>* (C, yvec)\<close> \<open>xvec \<sharp>* (C, yvec)\<close> 
  have "A\<^sub>P \<sharp>* C" and "A\<^sub>Q \<sharp>* C" and "xvec \<sharp>* C" and "A\<^sub>P \<sharp>* yvec" and "A\<^sub>Q \<sharp>* yvec" and "xvec \<sharp>* yvec"
    by simp+

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" 
   and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K" by fact+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>yvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
       \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close>
  obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "xvec \<sharp>* M'" and "yvec \<sharp>* M'" and "A\<^sub>Q \<sharp>* M'"
    by(rule_tac B="xvec@yvec@A\<^sub>Q" in obtainPrefix) (assumption | force)+ 
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>yvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
       \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* yvec\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
  obtain K' where KeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'" and "xvec \<sharp>* K'" and "yvec \<sharp>* K'" and "A\<^sub>P \<sharp>* K'"
    by(rule_tac B="xvec@yvec@A\<^sub>P" in obtainPrefix) (assumption | force | metis freshChainSym)+

  from MeqK KeqK' have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
  with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
    by(rule_tac inputRenameSubject) (assumption | force)+
  moreover note FrP \<open>distinct A\<^sub>P\<close>
  moreover from MeqK MeqM' have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
  with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
    by(rule_tac outputRenameSubject) (assumption | force)+
  moreover note FrQ \<open>distinct A\<^sub>Q\<close>
  moreover from MeqM' KeqK' MeqK have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* C\<close>
                \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* N\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
                \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* M'\<close> \<open>xvec \<sharp>* K'\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* C\<close> \<open>yvec \<sharp>* M'\<close> \<open>yvec \<sharp>* K'\<close> \<open>distinct xvec\<close>
  ultimately show ?case
    by(rule_tac rComm1)
next
  case(cComm2 \<Psi>\<^sub>Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P K Q' A\<^sub>Q)
  from \<open>A\<^sub>P \<sharp>* (C, yvec)\<close> \<open>A\<^sub>Q \<sharp>* (C, yvec)\<close> \<open>xvec \<sharp>* (C, yvec)\<close> 
  have "A\<^sub>P \<sharp>* C" and "A\<^sub>Q \<sharp>* C" and "xvec \<sharp>* C" and "A\<^sub>P \<sharp>* yvec" and "A\<^sub>Q \<sharp>* yvec" and "xvec \<sharp>* yvec"
    by simp+

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" 
   and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K" by fact+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>yvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
       \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* yvec\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
  obtain M' where MeqM': "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "xvec \<sharp>* M'" and "yvec \<sharp>* M'" and "A\<^sub>Q \<sharp>* M'"
    by(rule_tac B="xvec@yvec@A\<^sub>Q" in obtainPrefix) (assumption | force)+ 
  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>yvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close>
       \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* yvec\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> 
  obtain K' where KeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'" and "xvec \<sharp>* K'" and "yvec \<sharp>* K'" and "A\<^sub>P \<sharp>* K'"
    by(rule_tac B="xvec@yvec@A\<^sub>P" in obtainPrefix) (assumption | force | metis freshChainSym)+

  from MeqK KeqK' have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans)
  with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
    by(rule_tac outputRenameSubject) (assumption | force)+
  moreover note FrP \<open>distinct A\<^sub>P\<close>
  moreover from MeqK MeqM' have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
  with \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close>
  have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
    by(rule_tac inputRenameSubject) (assumption | force)+
  moreover note FrQ \<open>distinct A\<^sub>Q\<close>
  moreover from MeqM' KeqK' MeqK have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
    by(metis statEqEnt Associativity Commutativity Composition chanEqTrans chanEqSym)
  moreover note \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* C\<close>
                \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>A\<^sub>Q \<sharp>* N\<close> \<open>A\<^sub>Q \<sharp>* Q'\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* C\<close>
                \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* M'\<close> \<open>xvec \<sharp>* K'\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* C\<close> \<open>yvec \<sharp>* M'\<close> \<open>yvec \<sharp>* K'\<close> \<open>distinct xvec\<close>
  ultimately show ?case
    by(rule_tac rComm2)
qed

lemma inputCases[consumes 1, case_names cInput]:
  fixes \<Psi>   :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"  
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'"  
  and     rInput: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

  shows "Prop \<alpha> P'"
proof -
  {
    fix xvec N P
    assume Trans: "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'"
       and "xvec \<sharp>* \<Psi>" and "xvec \<sharp>* M" and "xvec \<sharp>* \<alpha>" and "xvec \<sharp>* P'" and "distinct xvec"
       and rInput: "\<And>K Tvec. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec\<rbrakk> \<Longrightarrow> Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"

    from Trans have "bn \<alpha> = []"
      apply -
      by(ind_cases "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P'") (auto simp add: residualInject)
    from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
    have "length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')" by simp
    note Trans
    moreover have "length xvec = inputLength(M\<lparr>\<lambda>*xvec N\<rparr>.P)" by auto
    moreover note \<open>distinct xvec\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
    moreover obtain x::name where "x \<sharp> \<Psi>" and "x \<sharp> P" and "x \<sharp> M" and "x \<sharp> xvec" and "x \<sharp> \<alpha>" and "x \<sharp> P'" and "x \<sharp> N"
      by(generate_fresh "name") auto
    ultimately have "Prop \<alpha> P'" using \<open>bn \<alpha> = []\<close> \<open>xvec \<sharp>* \<Psi>\<close>\<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* \<alpha>\<close> \<open>xvec \<sharp>* P'\<close>
      apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ C x])  
      apply(force simp add: residualInject psi.inject rInput)
      by(fastforce simp add: residualInject psi.inject inputChainFresh)+
  }
  note Goal = this
  moreover obtain p :: "name prm" where "(p \<bullet> xvec) \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* M" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* P"
                                    and "(p \<bullet> xvec) \<sharp>* \<alpha>" and "(p \<bullet> xvec) \<sharp>* P'" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                    and "distinctPerm p"
    by(rule_tac xvec=xvec and c="(\<Psi>, M, N, P, \<alpha>, P')" in name_list_avoiding) auto
  from Trans \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "\<Psi> \<rhd> M\<lparr>\<lambda>*(p \<bullet> xvec) (p \<bullet> N)\<rparr>.(p \<bullet> P) \<longmapsto>\<alpha> \<prec> P'"
    by(simp add: inputChainAlpha')
  moreover {
    fix K Tvec
    assume "\<Psi> \<turnstile> M \<leftrightarrow> K"
    moreover assume "set(p \<bullet> xvec) \<subseteq> supp(p \<bullet> N)"
    hence "(p \<bullet> set(p \<bullet> xvec)) \<subseteq> (p \<bullet> supp(p \<bullet> N))" by simp
    with \<open>distinctPerm p\<close> have "set xvec \<subseteq> supp N" by(simp add: eqvts)
    moreover assume "length(p \<bullet> xvec) = length(Tvec::'a list)"
    hence "length xvec = length Tvec" by simp
    moreover assume "distinct xvec"
    ultimately have "Prop (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])" 
      by(rule rInput)
    with \<open>length xvec = length Tvec\<close> S \<open>distinctPerm p\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
    have "Prop (K\<lparr>(p \<bullet> N)[(p \<bullet> xvec)::=Tvec]\<rparr>) ((p \<bullet> P)[(p \<bullet> xvec)::=Tvec])"
      by(simp add: renaming substTerm.renaming)
  }
  moreover from Trans have "distinct xvec" by(rule inputDistinct)
  hence "distinct(p \<bullet> xvec)" by simp
  ultimately show ?thesis using \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> \<open>(p \<bullet> xvec) \<sharp>* \<alpha>\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>distinct xvec\<close>
    by(rule_tac Goal) assumption+
qed

lemma outputCases[consumes 1, case_names cOutput]:
  fixes \<Psi> :: 'b
  and   M  :: 'a
  and   N  :: 'a
  and   P  :: "('a, 'b, 'c) psi"  
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P'"
  and     "\<And>K. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop (K\<langle>N\<rangle>) P"

  shows "Prop \<alpha> P'"
using assms
by(cases rule: semantics.cases) (auto simp add: residualInject psi.inject)

lemma caseCases[consumes 1, case_names cCase]:
  fixes \<Psi> :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<alpha>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes Trans: "\<Psi> \<rhd> (Cases Cs) \<longmapsto> Rs"
  and     rCase: "\<And>\<phi> P. \<lbrakk>\<Psi> \<rhd> P \<longmapsto> Rs; (\<phi>, P) mem Cs; \<Psi> \<turnstile> \<phi>; guarded P\<rbrakk> \<Longrightarrow> Prop"

  shows "Prop"
using assms
by(cases rule: semantics.cases) (auto simp add: residualInject psi.inject)

lemma resCases[consumes 7, case_names cOpen cRes]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     rOpen: "\<And>M xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> P'); y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec\<rbrakk> \<Longrightarrow>
                                         Prop (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> Prop \<alpha> (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop \<alpha> P'"
proof -
  from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
  have "length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')" by simp
  note Trans
  moreover have "length [] = inputLength(\<lparr>\<nu>x\<rparr>P)" and "distinct []"
    by(auto simp add: inputLength_inputLength'_inputLength''.simps)
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  ultimately show ?thesis using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>distinct(bn \<alpha>)\<close>
    apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ _ x x]) 
    apply(auto simp add: psi.inject alpha abs_fresh residualInject boundOutputApp boundOutput.inject eqvts)
    apply(subgoal_tac "y \<in> supp Na")
    apply(rule_tac rOpen)
    apply(auto simp add: residualInject boundOutputApp)
    apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm eqvts)
    by(rule rScope)
qed

lemma resCases'[consumes 7, case_names cOpen cRes]:
  fixes \<Psi>    :: 'b
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"
  and     "x \<sharp> P'"
  and     "bn \<alpha> \<sharp>* \<Psi>"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     rOpen: "\<And>M xvec yvec y N P'. \<lbrakk>\<Psi> \<rhd> ([(x, y)] \<bullet> P) \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'; y \<in> supp N;
                                         x \<sharp> N; x \<sharp> P'; x \<noteq> y; y \<sharp> xvec; y \<sharp> yvec; y \<sharp> M; distinct xvec; distinct yvec;
                                         xvec \<sharp>* \<Psi>; y \<sharp> \<Psi>; yvec \<sharp>* \<Psi>; xvec \<sharp>* P; y \<sharp> P; yvec \<sharp>* P; xvec \<sharp>* M; y \<sharp> M;
                                         yvec \<sharp>* M; xvec \<sharp>* yvec\<rbrakk> \<Longrightarrow>
                                         Prop (M\<lparr>\<nu>*(xvec@y#yvec)\<rparr>\<langle>N\<rangle>) P'"
  and     rScope:  "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> Prop \<alpha> (\<lparr>\<nu>x\<rparr>P')"

  shows "Prop \<alpha> P'"
proof -
  from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
  have "length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')" by simp
  note Trans
  moreover have "length [] = inputLength(\<lparr>\<nu>x\<rparr>P)" and "distinct []"
    by(auto simp add: inputLength_inputLength'_inputLength''.simps)
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  moreover note \<open>length(bn \<alpha>) = residualLength(\<alpha> \<prec> P')\<close> \<open>distinct(bn \<alpha>)\<close>
  ultimately show ?thesis using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P'\<close> \<open>distinct(bn \<alpha>)\<close>
    apply(cases rule: semanticsCases[of _ _ _ _ _ _ _ _ _ _ x x]) 
    apply(auto simp add: psi.inject alpha abs_fresh residualInject boundOutputApp boundOutput.inject eqvts)
    apply(subgoal_tac "y \<in> supp Na")
    apply(rule_tac rOpen)
    apply(auto simp add: residualInject boundOutputApp)
    apply(drule_tac pi="[(x, y)]" in semantics.eqvt)
    apply(simp add: calc_atm eqvts)
    apply(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
    apply(simp add: calc_atm eqvts)
    by(rule rScope)
qed

abbreviation
  statImpJudge ("_ \<hookrightarrow> _" [80, 80] 80)
  where "\<Psi> \<hookrightarrow> \<Psi>' \<equiv> AssertionStatImp \<Psi> \<Psi>'"

lemma statEqTransition:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto> Rs"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<longmapsto> Rs"
using assms
proof(nominal_induct avoiding: \<Psi>' rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P \<Psi>')
  from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>' \<turnstile> M \<leftrightarrow> K"
    by(simp add: AssertionStatImp_def AssertionStatEq_def)
  thus ?case using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
    by(rule Input)
next
  case(Output \<Psi> M K N P \<Psi>')
  from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>' \<turnstile> M \<leftrightarrow> K"
    by(simp add: AssertionStatImp_def AssertionStatEq_def) 
  thus ?case by(rule semantics.Output)
next
  case(Case \<Psi> P Rs \<phi> Cs \<Psi>')
  then have "\<Psi>' \<rhd> P \<longmapsto> Rs" by(rule_tac Case)
  moreover note \<open>(\<phi>, P) mem Cs\<close>
  moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> have "\<Psi>' \<turnstile> \<phi>"
    by(simp add: AssertionStatImp_def AssertionStatEq_def)
  ultimately show ?case using \<open>guarded P\<close> by(rule semantics.Case)
next
  case(cPar1 \<Psi> \<Psi>Q P \<alpha> P' xvec Q \<Psi>')
  thus ?case
    by(rule_tac Par1) (auto intro: Composition)
next
  case(cPar2 \<Psi> \<Psi>P Q \<alpha> Q' xvec P \<Psi>')
  thus ?case
    by(rule_tac Par2) (auto intro: Composition)
next
  case(cComm1 \<Psi> \<Psi>Q P M N P' xvec \<Psi>P Q K zvec Q' yvec \<Psi>')
  thus ?case
    by(clarsimp, rule_tac Comm1) (blast intro: Composition statEqEnt)+
next
  case(cComm2 \<Psi> \<Psi>Q P M zvec N P' xvec \<Psi>P Q K Q' yvec \<Psi>')
  thus ?case
    by(clarsimp, rule_tac Comm2) (blast intro: Composition statEqEnt)+
next
  case(cOpen \<Psi> P M xvec N P' x yvec \<Psi>')
  thus ?case by(force intro: Open)
next
  case(cScope \<Psi> P \<alpha> P' x \<Psi>')
  thus ?case by(force intro: Scope)
next
  case(Bang \<Psi> P Rs \<Psi>')
  thus ?case by(force intro: semantics.Bang)
qed

lemma actionPar1Dest':
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* R"
  and     "bn \<beta> \<sharp>* R"

  obtains T where "P = T \<parallel> R" and "\<alpha> \<prec> T = \<beta> \<prec> Q"
using assms
apply(cases rule: actionCases[where \<alpha>=\<alpha>])
apply(auto simp add: residualInject)
by(drule_tac boundOutputPar1Dest) auto

lemma actionPar2Dest':
  fixes \<alpha> :: "('a::fs_name) action"
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   \<beta> :: "('a::fs_name) action"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<alpha> \<prec> P = \<beta> \<prec> (Q \<parallel> R)"
  and     "bn \<alpha> \<sharp>* Q"
  and     "bn \<beta> \<sharp>* Q"

  obtains T where "P = Q \<parallel> T" and "\<alpha> \<prec> T = \<beta> \<prec> R"
using assms
apply(cases rule: actionCases[where \<alpha>=\<alpha>])
apply(auto simp add: residualInject)
by(drule_tac boundOutputPar2Dest) auto

lemma expandNonTauFrame:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   C    :: "'d::fs_name"
  and   C'   :: "'e::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* C"
  and     "A\<^sub>P \<sharp>* C'"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* C'"
  and     "\<alpha> \<noteq> \<tau>"

  obtains p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinctPerm p" and
                              "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" and
                              "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'" and "distinct A\<^sub>P'"
proof -
  assume A: "\<And>p \<Psi>' \<Psi>\<^sub>P' A\<^sub>P'.
        \<lbrakk>set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); (p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'; distinctPerm p;
                              extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>; A\<^sub>P' \<sharp>* P'; A\<^sub>P' \<sharp>* \<alpha>; A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>);
                              A\<^sub>P' \<sharp>* C; (bn(p \<bullet> \<alpha>)) \<sharp>* C'; (bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>; (bn(p \<bullet> \<alpha>)) \<sharp>* P'; distinct A\<^sub>P'\<rbrakk>
        \<Longrightarrow> thesis"

  from Trans have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)

  with Trans \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "A\<^sub>P \<sharp>* P'"
    by(drule_tac freeFreshChainDerivative) auto
  {
    fix X :: "name list"
    and Y :: "'b list"
    and Z :: "('a, 'b, 'c) psi list"

    assume "bn \<alpha> \<sharp>* X" and "bn \<alpha> \<sharp>* Y" and "bn \<alpha> \<sharp>* Z" and "A\<^sub>P \<sharp>* X" and "A\<^sub>P \<sharp>* Y" and "A\<^sub>P \<sharp>* Z" 

    with assms obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinctPerm p"
                                      and "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                      and "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                      and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                      and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
      using \<open>A\<^sub>P \<sharp>* P'\<close> \<open>distinct(bn \<alpha>)\<close>
    proof(nominal_induct \<Psi> P Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P avoiding: C C' \<alpha> P' X Y Z arbitrary: thesis rule: semanticsFrameInduct)
      case(cAlpha \<Psi> P A\<^sub>P \<Psi>\<^sub>P p C C' \<alpha> P' X Y Z)
      then obtain q \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where Sq: "set q \<subseteq> set(bn \<alpha>) \<times> set(bn(q \<bullet> \<alpha>))" and PeqP': "(q \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinctPerm q"
                                  and FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (q \<bullet> \<alpha>)"
                                  and "A\<^sub>P' \<sharp>* C" and "(bn(q \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(q \<bullet> \<alpha>)) \<sharp>* P'"
                                  and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                  and "(bn(q \<bullet> \<alpha>)) \<sharp>* X" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(q \<bullet> \<alpha>)) \<sharp>* Z"
        by metis

      have Sp: "set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)" by fact

      from Sq have "(p \<bullet> set q) \<subseteq> p \<bullet> (set(bn \<alpha>) \<times> set(bn(q \<bullet> \<alpha>)))"
        by(simp add: subsetClosed)
      hence "set(p \<bullet> q) \<subseteq> set(bn(p \<bullet> \<alpha>)) \<times> set(p \<bullet> bn(q \<bullet> \<alpha>))"
        by(simp add: eqvts)
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> Sp have "set(p \<bullet> q) \<subseteq> set(bn \<alpha>) \<times> set(bn((p \<bullet> q) \<bullet> \<alpha>))"
        by(simp add: perm_compose bnEqvt[symmetric])
      moreover from PeqP' have "(p \<bullet> (q \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')"
        by(simp add: AssertionStatEqClosed)
      hence "((p \<bullet> q) \<bullet> p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')"
        apply(subst perm_compose[symmetric])
        by(simp add: eqvts)
      moreover from \<open>distinctPerm q\<close> have "distinctPerm (p \<bullet> q)"
        by simp
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* C'\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> C')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* C'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* C'\<close> Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* C'"
        by(simp add: perm_compose bnEqvt[symmetric])
      moreover from FrP' have "(p \<bullet> extractFrame P') = p \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" by simp
      with \<open>A\<^sub>P \<sharp>* P'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> Sp have "extractFrame P' = \<langle>p \<bullet> A\<^sub>P', p \<bullet> \<Psi>\<^sub>P'\<rangle>"
        by(simp add: eqvts)
      moreover from \<open>A\<^sub>P' \<sharp>* P'\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> P')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* P'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* P'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* \<alpha>\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> \<alpha>)"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* \<alpha>" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* C\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> C)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* C\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* C\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* C" by simp
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* \<alpha>\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> \<alpha>)"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* \<alpha>"
        by(simp add: perm_compose eqvts)
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* P'\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> P')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* P'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* P'"
        by(simp add: perm_compose eqvts)
      moreover from \<open>A\<^sub>P' \<sharp>* (q \<bullet> \<alpha>)\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> q \<bullet> \<alpha>)"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with Sp \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* ((p \<bullet> q) \<bullet> \<alpha>)"
        by(simp add: perm_compose)
      moreover from \<open>A\<^sub>P' \<sharp>* X\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> X)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* X\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* X\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* X" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Y\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Y)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* Y\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Y\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Z\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Z)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* Z\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Z\<close> Sp have "(p \<bullet> A\<^sub>P') \<sharp>* Z" by simp
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* X\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> X)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* X\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* X\<close> Sp have "bn((p \<bullet> q) \<bullet>  \<alpha>) \<sharp>* X"
        by(simp add: perm_compose eqvts)
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Y\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> Y)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Y\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Y\<close> Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* Y"
        by(simp add: perm_compose eqvts)
      moreover from \<open>(bn(q \<bullet> \<alpha>)) \<sharp>* Z\<close> have "(p \<bullet> bn(q \<bullet> \<alpha>)) \<sharp>* (p \<bullet> Z)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<alpha>\<close> \<open>A\<^sub>P \<sharp>* Z\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Z\<close> Sp have "bn((p \<bullet> q) \<bullet> \<alpha>) \<sharp>* Z"
        by(simp add: perm_compose eqvts)
      moreover from \<open>distinct A\<^sub>P'\<close> have "distinct(p \<bullet> A\<^sub>P')" by simp
      ultimately show ?case
        by(rule_tac cAlpha)
    next
      case(cInput \<Psi> M K xvec N Tvec P C C' \<alpha> P' X Y Z)
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame(P[xvec::=Tvec]) = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                      and "A\<^sub>P \<sharp>* (C, P[xvec::=Tvec], \<alpha>, P', X, Y, Z, N)"
        by(rule freshFrame)
      moreover have "\<one> \<otimes> \<Psi>\<^sub>P \<simeq> \<Psi>\<^sub>P"
        by(blast intro: Identity Commutativity AssertionStatEqTrans)
      ultimately show ?case
        by(rule_tac cInput) (assumption | simp add: residualInject)+
    next
      case(cOutput \<Psi> M K N P C C' \<alpha> P' X Y Z)
      moreover obtain A\<^sub>P \<Psi>\<^sub>P where "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                               and "A\<^sub>P \<sharp>* (C, C', P, \<alpha>, N, P', X, Y, Z)"
        by(rule freshFrame)
      moreover have "\<one> \<otimes> \<Psi>\<^sub>P \<simeq> \<Psi>\<^sub>P"
        by(blast intro: Identity Commutativity AssertionStatEqTrans)
      ultimately show ?case by(simp add: residualInject)
    next
      case(cCase \<Psi> P \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P' X Y Z)
      moreover from \<open>bn \<alpha> \<sharp>* (Cases Cs)\<close> \<open>(\<phi>, P) mem Cs\<close> have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"
                                         and FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                         and PeqP': "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                         and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                         and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
                                         and "distinctPerm p" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                         and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
        by(rule_tac cCase) (assumption | simp (no_asm_use))+
      moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "(p \<bullet> \<Psi>\<^sub>P) \<simeq> (p \<bullet> \<one>)"
        by(simp add: AssertionStatEqClosed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<simeq> \<one>" by(simp add: permBottom)
      with PeqP' have "(\<one> \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
        by(metis Identity AssertionStatEqTrans composition' Commutativity Associativity AssertionStatEqSym)
      ultimately show ?case using cCase \<open>bn \<alpha> \<sharp>* P\<close>
        by(rule_tac cCase(20)) (assumption | simp)+
    next
      case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C C' \<alpha>' PQ' X Y Z)
      have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
        by fact+

      note \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
      moreover from \<open>bn \<alpha>' \<sharp>* (P \<parallel> Q)\<close> have "bn \<alpha>' \<sharp>* P" and "bn \<alpha>' \<sharp>* Q" by simp+    
      moreover with FrP FrQ \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "bn \<alpha>' \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q" 
        by(force dest: extractFrameFreshChain)+
 
      moreover from \<open>bn \<alpha>' \<sharp>* X\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "bn \<alpha>' \<sharp>* (X@A\<^sub>Q)" by simp
      moreover from \<open>bn \<alpha>' \<sharp>* Y\<close> \<open>bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q\<close> have "bn \<alpha>' \<sharp>* (\<Psi>\<^sub>Q#Y)" by simp
      moreover from \<open>bn \<alpha>' \<sharp>* Z\<close> \<open>bn \<alpha>' \<sharp>* Q\<close> have "bn \<alpha>' \<sharp>* (Q#Z)" by simp
      moreover from \<open>A\<^sub>P \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>P \<sharp>* (X@A\<^sub>Q)" by simp
      moreover from \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> have "A\<^sub>P \<sharp>* (\<Psi>\<^sub>Q#Y)" by force
      moreover from \<open>A\<^sub>P \<sharp>* Z\<close> \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* (Q#Z)" by simp
      moreover from \<open>\<alpha> \<prec> (P' \<parallel> Q) = \<alpha>' \<prec> PQ'\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha>' \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close>
      obtain P'' where A: "\<alpha> \<prec> P' = \<alpha>' \<prec> P''" and "PQ' = P'' \<parallel> Q"
        by(metis actionPar1Dest')
      moreover from \<open>A\<^sub>P \<sharp>* PQ'\<close> \<open>PQ' = P'' \<parallel> Q\<close> have "A\<^sub>P \<sharp>* P''" by simp
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set (bn(p \<bullet> \<alpha>'))" and PeqP': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                        and "distinctPerm p" and "(bn(p \<bullet> \<alpha>')) \<sharp>* C'" and FrP': "extractFrame P'' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                        and "A\<^sub>P' \<sharp>* P''" and "A\<^sub>P' \<sharp>* \<alpha>'" "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>P' \<sharp>* C" 
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'" and "(bn(p \<bullet> \<alpha>')) \<sharp>* P''" and "distinct A\<^sub>P'"
                                        and "A\<^sub>P' \<sharp>* (X @ A\<^sub>Q)" and "A\<^sub>P' \<sharp>* (\<Psi>\<^sub>Q#Y)"
                                        and "A\<^sub>P' \<sharp>* (Q#Z)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (X @ A\<^sub>Q)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (\<Psi>\<^sub>Q#Y)"
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* (Q#Z)" using cPar1
        by(rule_tac cPar1)

      then have "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q"  and "A\<^sub>P' \<sharp>* Y" 
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* A\<^sub>Q" and "(bn(p \<bullet> \<alpha>')) \<sharp>* X" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Z" and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>Q"
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* Q"
        by(simp del: freshChainSimps)+

      from \<open>A\<^sub>Q \<sharp>* PQ'\<close> \<open>PQ' = P'' \<parallel> Q\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> FrP' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'"
        by(force dest: extractFrameFreshChain)
      note S
      moreover from PeqP' have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P' \<otimes> (p \<bullet> \<Psi>\<^sub>Q)"
        by(simp add: eqvts) (metis Composition Associativity AssertionStatEqTrans AssertionStatEqSym Commutativity)
      with \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q\<close> S have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q"
        by simp
      moreover from \<open>PQ' = P'' \<parallel> Q\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'\<close> \<open>A\<^sub>Q \<sharp>* PQ'\<close> FrP' FrQ have "extractFrame PQ' = \<langle>(A\<^sub>P'@A\<^sub>Q), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by simp
      moreover note \<open>distinctPerm p\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* C'\<close>
      moreover from \<open>A\<^sub>P' \<sharp>* P''\<close> \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>PQ' = P'' \<parallel> Q\<close> have "A\<^sub>P' \<sharp>* PQ'" by simp
      moreover note \<open>A\<^sub>Q \<sharp>* PQ'\<close> \<open>A\<^sub>P' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'\<close>
      moreover from \<open>bn \<alpha>' \<sharp>* Q\<close> have "(bn(p \<bullet> \<alpha>')) \<sharp>* (p \<bullet> Q)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bnEqvt[symmetric])
      with \<open>bn \<alpha> \<sharp>* Q\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Q\<close> S have "(bn(p \<bullet> \<alpha>')) \<sharp>* Q" by simp
      with \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* P''\<close> \<open>PQ' = P'' \<parallel> Q\<close> have "(bn(p \<bullet> \<alpha>')) \<sharp>* PQ'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* \<alpha>'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* C" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* X\<close> \<open>A\<^sub>Q \<sharp>* X\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* X" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* Y\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>A\<^sub>Q \<sharp>* Z\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Z" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* PQ'\<close> \<open>A\<^sub>Q \<sharp>* PQ'\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* PQ'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* \<alpha>'" by simp
      moreover from \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<alpha>')"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bnEqvt[symmetric])
      with S \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* (p \<bullet> \<alpha>')"
        by simp
      with \<open>A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>Q\<close> S have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* (p \<bullet> \<alpha>')"
        by simp
      moreover from \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>distinct A\<^sub>P'\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(A\<^sub>P'@A\<^sub>Q)" by auto
      moreover note \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* X\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Y\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Z\<close>
      ultimately show ?case using cPar1
        by metis
    next
      case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C C' \<alpha>' PQ' X Y Z)
      have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
        by fact+

      note \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close>
      moreover from \<open>bn \<alpha>' \<sharp>* (P \<parallel> Q)\<close> have "bn \<alpha>' \<sharp>* Q" and "bn \<alpha>' \<sharp>* P" by simp+    
      moreover with FrP FrQ \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> have "bn \<alpha>' \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha>' \<sharp>* \<Psi>\<^sub>Q" 
        by(force dest: extractFrameFreshChain)+
 
      moreover from \<open>bn \<alpha>' \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> have "bn \<alpha>' \<sharp>* (X@A\<^sub>P)" by simp
      moreover from \<open>bn \<alpha>' \<sharp>* Y\<close> \<open>bn \<alpha>' \<sharp>* \<Psi>\<^sub>P\<close> have "bn \<alpha>' \<sharp>* (\<Psi>\<^sub>P#Y)" by simp
      moreover from \<open>bn \<alpha>' \<sharp>* Z\<close> \<open>bn \<alpha>' \<sharp>* P\<close> have "bn \<alpha>' \<sharp>* (P#Z)" by simp
      moreover from \<open>A\<^sub>Q \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* (X@A\<^sub>P)" by simp
      moreover from \<open>A\<^sub>Q \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "A\<^sub>Q \<sharp>* (\<Psi>\<^sub>P#Y)" by force
      moreover from \<open>A\<^sub>Q \<sharp>* Z\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* (P#Z)" by simp
      moreover from \<open>\<alpha> \<prec> (P \<parallel> Q') = \<alpha>' \<prec> PQ'\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha>' \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close>
      obtain Q'' where A: "\<alpha> \<prec> Q' = \<alpha>' \<prec> Q''" and "PQ' = P \<parallel> Q''"
        by(metis actionPar2Dest')
      moreover from \<open>A\<^sub>Q \<sharp>* PQ'\<close> \<open>PQ' = P \<parallel> Q''\<close> have "A\<^sub>Q \<sharp>* Q''" by simp
      ultimately obtain p \<Psi>' A\<^sub>Q' \<Psi>\<^sub>Q' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set (bn(p \<bullet> \<alpha>'))" and QeqQ': "((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>Q'"
                                        and "distinctPerm p" and "(bn(p \<bullet> \<alpha>')) \<sharp>* C'" and FrQ': "extractFrame Q'' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>"
                                        and "A\<^sub>Q' \<sharp>* Q''" and "A\<^sub>Q' \<sharp>* \<alpha>'" "A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>Q' \<sharp>* C" 
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Q''" and "distinct A\<^sub>Q'"
                                        and "A\<^sub>Q' \<sharp>* (X @ A\<^sub>P)" and "A\<^sub>Q' \<sharp>* (\<Psi>\<^sub>P#Y)"
                                        and "A\<^sub>Q' \<sharp>* (P#Z)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (X @ A\<^sub>P)" and "(bn(p \<bullet> \<alpha>')) \<sharp>* (\<Psi>\<^sub>P#Y)"
                                        and "(bn(p \<bullet> \<alpha>')) \<sharp>* (P#Z)" using cPar2
        by(rule_tac cPar2)

      then have "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* A\<^sub>P" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P"  and "A\<^sub>Q' \<sharp>* Y" 
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* A\<^sub>P" and "(bn(p \<bullet> \<alpha>')) \<sharp>* X" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>')) \<sharp>* Z" and "(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>P"
            and "(bn(p \<bullet> \<alpha>')) \<sharp>* P"
        by(simp del: freshChainSimps)+

      from \<open>A\<^sub>P \<sharp>* PQ'\<close> \<open>PQ' = P \<parallel> Q''\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> FrQ' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'"
        by(force dest: extractFrameFreshChain)
      note S
      moreover from QeqQ' have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q'"
        by(simp add: eqvts) (metis Composition Associativity AssertionStatEqTrans AssertionStatEqSym Commutativity)
      with \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* \<Psi>\<^sub>P\<close> \<open>bn \<alpha>' \<sharp>* \<Psi>\<^sub>P\<close> S have "((p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q)) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'"
        by simp
      moreover from \<open>PQ' = P \<parallel> Q''\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'\<close> \<open>A\<^sub>P \<sharp>* PQ'\<close> FrQ' FrP have "extractFrame PQ' = \<langle>(A\<^sub>P@A\<^sub>Q'), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'\<rangle>"
        by simp
      moreover note \<open>distinctPerm p\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* C'\<close>
      moreover from \<open>A\<^sub>Q' \<sharp>* Q''\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>PQ' = P \<parallel> Q''\<close> have "A\<^sub>Q' \<sharp>* PQ'" by simp
      moreover note \<open>A\<^sub>Q \<sharp>* PQ'\<close> \<open>A\<^sub>Q' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>'\<close> \<open>A\<^sub>Q' \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* \<alpha>'\<close>
      moreover from \<open>bn \<alpha>' \<sharp>* Q\<close> have "(bn(p \<bullet> \<alpha>')) \<sharp>* (p \<bullet> Q)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bnEqvt[symmetric])
      with \<open>bn \<alpha> \<sharp>* P\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* P\<close> S have "(bn(p \<bullet> \<alpha>')) \<sharp>* P" by simp
      with \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Q''\<close> \<open>PQ' = P \<parallel> Q''\<close> have "(bn(p \<bullet> \<alpha>')) \<sharp>* PQ'" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* \<alpha>'" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* C\<close> \<open>A\<^sub>P \<sharp>* C\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* C" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* X\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* X" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* Y\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* Z\<close> \<open>A\<^sub>P \<sharp>* Z\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* PQ'\<close> \<open>A\<^sub>P \<sharp>* PQ'\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* PQ'" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* \<alpha>'" by simp
      moreover from \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<alpha>')"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst] bnEqvt[symmetric])
      with S \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* (p \<bullet> \<alpha>')"
        by simp
      with \<open>A\<^sub>Q' \<sharp>* (p \<bullet> \<alpha>')\<close> \<open>A\<^sub>P \<sharp>* \<alpha>'\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* A\<^sub>P\<close> S have "(A\<^sub>P@A\<^sub>Q') \<sharp>* (p \<bullet> \<alpha>')"
        by simp
      moreover note \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* X\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Y\<close> \<open>(bn(p \<bullet> \<alpha>')) \<sharp>* Z\<close>
      moreover from \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q'\<close> have "distinct(A\<^sub>P@A\<^sub>Q')" by auto
      ultimately show ?case using cPar2
        by metis
    next
      case cComm1
      thus ?case by(simp add: residualInject)
    next
      case cComm2
      thus ?case by(simp add: residualInject)
    next
      case(cOpen \<Psi> P M xvec1 xvec2 N P' x A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P'' X Y Z)
      from \<open>M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>distinct(bn \<alpha>)\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>x \<sharp> \<alpha>\<close>
      obtain yvec1 y yvec2 N' where yvecEq: "bn \<alpha> = yvec1@y#yvec2" and P'eqP'': "\<lparr>\<nu>*(xvec1@xvec2)\<rparr>N \<prec>' P' = \<lparr>\<nu>*(yvec1@yvec2)\<rparr>([(x, y)] \<bullet> N') \<prec>' ([(x, y)] \<bullet> P'')" and "A\<^sub>P \<sharp>* N'" and Subj: "subject \<alpha> = Some M" and "x \<sharp> N'" and \<alpha>eq: "\<alpha> = M\<lparr>\<nu>*(yvec1@y#yvec2)\<rparr>\<langle>N'\<rangle>"
        apply(cases rule: actionCases[where \<alpha>=\<alpha>])
        apply(auto simp add: residualInject)
        apply(rule boundOutputOpenDest)
        by assumption auto
      note \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close>
      moreover from Subj yvecEq \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "yvec1 \<sharp>* M" "yvec2 \<sharp>* M" by simp+
      moreover from yvecEq \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "A\<^sub>P \<sharp>* (yvec1@yvec2)" by simp
      moreover note \<open>A\<^sub>P \<sharp>* C\<close>
      moreover from yvecEq  \<open>bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>x \<sharp> \<alpha>\<close> have "(yvec1@yvec2) \<sharp>* P" by simp
      moreover from yvecEq \<open>bn \<alpha> \<sharp>* C'\<close> \<open>bn \<alpha> \<sharp>* X\<close> \<open>bn \<alpha> \<sharp>* Y\<close> \<open>bn \<alpha> \<sharp>* Z\<close> \<open>distinct(bn \<alpha>)\<close> \<open>x \<sharp> \<alpha>\<close>
      have "(yvec1@yvec2) \<sharp>* C'" and "(yvec1@yvec2) \<sharp>* (x#y#X)" and "(yvec1@yvec2) \<sharp>* Y" and "(yvec1@yvec2) \<sharp>* Z"
        by simp+
      moreover from \<open>A\<^sub>P \<sharp>* X\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> yvecEq have "A\<^sub>P \<sharp>* (x#y#X)" by simp
      moreover note \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* Z\<close>
      moreover from \<open>A\<^sub>P \<sharp>* N'\<close> \<open>A\<^sub>P \<sharp>* P''\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> yvecEq have "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> N')" and  "A\<^sub>P \<sharp>* ([(x, y)] \<bullet> P'')"
        by simp+
      moreover from yvecEq \<open>distinct(bn \<alpha>)\<close> have "distinct(yvec1@yvec2)" by simp
      moreover from P'eqP'' have "M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>N\<rangle> \<prec> P' = M\<lparr>\<nu>*(yvec1@yvec2)\<rparr>\<langle>([(x, y)] \<bullet> N')\<rangle> \<prec> ([(x, y)] \<bullet> P'')"
        by(simp add: residualInject)
      ultimately obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set (yvec1@yvec2) \<times> set (p \<bullet> (yvec1@yvec2))" and PeqP': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                        and "distinctPerm p" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* C'" and FrP': "extractFrame([(x, y)] \<bullet> P'') = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                        and "A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> P'')" and "A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> N')" and "A\<^sub>P' \<sharp>* C" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')" and "A\<^sub>P' \<sharp>* M" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* (yvec1@yvec2)" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* M" and "distinct A\<^sub>P'"
                                        and "(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> P'')" and "(yvec1@yvec2) \<sharp>* A\<^sub>P'" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'"
                                        and "A\<^sub>P' \<sharp>* (x#y#X)" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* (x#y#X)"
                                        and "(p \<bullet> (yvec1@yvec2)) \<sharp>* Y" and "(p \<bullet> (yvec1@yvec2)) \<sharp>* Z" using \<open>A\<^sub>P \<sharp>* C'\<close>
        by(rule_tac cOpen(4)[where bd="x#y#X"]) (assumption | simp_all)+

      from \<open>A\<^sub>P' \<sharp>* (x#y#X)\<close> have "x \<sharp> A\<^sub>P'" and "y \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      from \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* (x#y#X)\<close> have "x \<sharp> (p \<bullet> (yvec1@yvec2))" and  "y \<sharp> (p \<bullet> (yvec1@yvec2))" and  "(p \<bullet> (yvec1@yvec2)) \<sharp>* X" by simp+

      from \<open>x \<sharp> \<alpha>\<close> yvecEq have "x \<sharp> yvec1" and "x \<noteq> y" and "x \<sharp> yvec2" by simp+
      from \<open>distinct(bn \<alpha>)\<close> yvecEq have "yvec1 \<sharp>* yvec2" and "y \<sharp> yvec1" and "y \<sharp> yvec2" by simp+
      from \<open>bn \<alpha> \<sharp>* C'\<close> yvecEq have "yvec1 \<sharp>* C'" and "y \<sharp> C'" and "yvec2 \<sharp>* C'" by simp+

      from S \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> p \<bullet> (yvec1@yvec2)\<close> yvecEq have "x \<sharp> p" by(rule_tac freshAlphaSwap) (assumption | simp)+
      from S \<open>distinct(bn \<alpha>)\<close> \<open>y \<sharp> p \<bullet> (yvec1@yvec2)\<close> yvecEq have "y \<sharp> p" by(rule_tac freshAlphaSwap) (assumption | simp)+

      from yvecEq S \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p \<bullet> (yvec1@yvec2)\<close> \<open>y \<sharp> p \<bullet> (yvec1@yvec2)\<close>
      have "set ((y, x)#p) \<subseteq> set(bn \<alpha>) \<times> set(bn(((y, x)#p) \<bullet> \<alpha>))"
        apply(simp add: bnEqvt[symmetric])
        by(auto simp add: eqvts calc_atm)

      moreover from PeqP' have "([(y, x)] \<bullet> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>')) \<simeq> [(y, x)] \<bullet> \<Psi>\<^sub>P'"
        by(simp add: AssertionStatEqClosed)
      hence "(((y, x)#p) \<bullet> \<Psi>\<^sub>P) \<otimes> ([(y, x)] \<bullet> \<Psi>') \<simeq> ([(y, x)] \<bullet> \<Psi>\<^sub>P')"
        by(simp add: eqvts)
      moreover from \<open>distinctPerm p\<close> S \<open>x \<noteq> y\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> have "distinctPerm((y, x)#p)"
        by simp
      moreover from FrP' have "([(x, y)] \<bullet> (extractFrame([(x, y)] \<bullet> P''))) = ([(x, y)] \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>)"
        by simp
      with \<open>x \<sharp> A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> have "extractFrame P'' = \<langle>A\<^sub>P', ([(y, x)] \<bullet> \<Psi>\<^sub>P')\<rangle>"
        by(simp add: eqvts name_swap)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> N'\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')\<close> have "([(y, x)] \<bullet> p \<bullet> (yvec1@yvec2)) \<sharp>* ([(y, x)] \<bullet> [(x, y)] \<bullet> N')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      hence "(((y, x)#p) \<bullet> (yvec1@yvec2)) \<sharp>* N'" by(simp add: name_swap) 
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> C\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> N'\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* N'" by(simp add: bnEqvt[symmetric]) (simp add: eqvts perm_compose calc_atm freshChainSimps)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> N'\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> P'')\<close> have "([(y, x)] \<bullet> p \<bullet> (yvec1@yvec2)) \<sharp>* ([(y, x)] \<bullet> [(x, y)] \<bullet> P'')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      hence "(((y, x)#p) \<bullet> (yvec1@yvec2)) \<sharp>* P''" by(simp add: name_swap) 
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> P''\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* P''" by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps) 
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> A\<^sub>P'\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'\<close> have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* A\<^sub>P'"
        by(simp add: eqvts freshChainSimps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> A\<^sub>P')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> A\<^sub>P'\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>y \<sharp> A\<^sub>P'\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* A\<^sub>P'" by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> C'\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* C'\<close> have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* C'"
        by(simp add: eqvts freshChainSimps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> C')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> C'\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>y \<sharp> C'\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* C'"  by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> X\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* X\<close> have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* X"
        by(simp add: eqvts freshChainSimps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> X)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> X\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>bn \<alpha> \<sharp>* X\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* X" by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> Y\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* Y\<close> have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* Y"
        by(simp add: eqvts freshChainSimps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> Y)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> Y\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>bn \<alpha> \<sharp>* Y\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* Y" by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps)
      moreover from \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> Z\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* Z\<close> have "(p \<bullet> (yvec1@x#yvec2)) \<sharp>* Z"
        by(simp add: eqvts freshChainSimps)
      hence "([(y, x)] \<bullet> p \<bullet> (yvec1@x#yvec2)) \<sharp>* ([(y, x)] \<bullet> Z)"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> yvec1\<close> \<open>x \<sharp> yvec2\<close> \<open>x \<noteq> y\<close> \<open>x \<sharp> Z\<close> \<open>y \<sharp> yvec1\<close> \<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>bn \<alpha> \<sharp>* Z\<close> yvecEq
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* Z" by(simp add: bnEqvt[symmetric]) (simp add: perm_compose calc_atm eqvts freshChainSimps)
      moreover from \<open>(yvec1@yvec2) \<sharp>* A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> yvecEq have "bn \<alpha> \<sharp>* A\<^sub>P'"
        by simp
      moreover from \<open>A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> N')\<close> have "([(x, y)] \<bullet> A\<^sub>P') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> N')"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> have "A\<^sub>P' \<sharp>* N'" by simp
      with \<open>A\<^sub>P' \<sharp>* M\<close> \<open>(yvec1@yvec2) \<sharp>* A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> \<alpha>eq have "A\<^sub>P' \<sharp>* \<alpha>" by simp
      moreover hence "(((y, x)#p) \<bullet> A\<^sub>P') \<sharp>* (((y, x)#p) \<bullet> \<alpha>)"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> S \<open>(yvec1@yvec2) \<sharp>* A\<^sub>P'\<close> \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* A\<^sub>P'\<close>
      have "A\<^sub>P' \<sharp>* (((y, x)#p) \<bullet> \<alpha>)" by(simp add: eqvts)
      moreover from \<open>A\<^sub>P' \<sharp>* ([(x, y)] \<bullet> P'')\<close> have "([(x, y)] \<bullet> A\<^sub>P') \<sharp>* ([(x, y)] \<bullet> [(x, y)] \<bullet> P'')"
        by(simp only: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>x \<sharp> A\<^sub>P'\<close> \<open>y \<sharp> A\<^sub>P'\<close> have "A\<^sub>P' \<sharp>* P''" by simp
      moreover from yvecEq \<alpha>eq \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* (yvec1@yvec2)\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> \<alpha>\<close> S \<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* M\<close>\<open>(p \<bullet> (yvec1@yvec2)) \<sharp>* ([(x, y)] \<bullet> N')\<close> \<open>y \<sharp> yvec1\<close>\<open>y \<sharp> yvec2\<close> \<open>x \<sharp> p\<close>
      have "bn(((y, x)#p) \<bullet> \<alpha>) \<sharp>* \<alpha>"
      apply(simp add: eqvts del: set_append) 
      apply(intro conjI)
      apply(simp add: perm_compose eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose eqvts del: set_append)
      apply(simp add: perm_compose eqvts swapStarFresh del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) swapStarFresh calc_atm eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(subst pt_fresh_star_bij[symmetric, OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"])
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      apply(subst pt_fresh_star_bij[symmetric, OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"])
      by(simp add: perm_compose freshChainSimps(6) calc_atm eqvts del: set_append)
      moreover note \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>P' \<sharp>* X\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>distinct A\<^sub>P'\<close>

      ultimately show ?case
        by(rule_tac cOpen)
    next
      case(cScope \<Psi> P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P C C' \<alpha>' P'' X Y Z)
      from \<open>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P' = \<alpha>' \<prec> P''\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> \<alpha>'\<close>
      obtain P''' where "\<alpha> \<prec> P' = \<alpha>' \<prec> P'''" and "P'' = \<lparr>\<nu>x\<rparr>P'''"
        apply(cases rule: actionCases[where \<alpha>=\<alpha>])
        apply(auto simp add: residualInject)
        by(metis boundOutputScopeDest)
      then obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>') \<times> set(bn(p \<bullet> \<alpha>'))" and PeqP': "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
                                  and "distinctPerm p" and "bn(p \<bullet> \<alpha>') \<sharp>* C'" and FrP': "extractFrame P''' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"
                                  and "A\<^sub>P' \<sharp>* P'''" and "A\<^sub>P' \<sharp>* \<alpha>'" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
                                  and "bn(p \<bullet> \<alpha>') \<sharp>* P'''" and "A\<^sub>P' \<sharp>* (x#X)" and "A\<^sub>P' \<sharp>* Y" and "bn(p \<bullet> \<alpha>') \<sharp>* \<alpha>'"
                                  and "A\<^sub>P' \<sharp>* Z" and "bn(p \<bullet> \<alpha>') \<sharp>* (x#X)" and "bn(p \<bullet> \<alpha>') \<sharp>* Y"
                                  and "bn(p \<bullet> \<alpha>') \<sharp>* Z" using cScope
        by(rule_tac cScope) (assumption | simp)+
      from \<open>A\<^sub>P' \<sharp>* (x#X)\<close> have "x \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      from \<open>bn(p \<bullet> \<alpha>') \<sharp>* (x#X)\<close> have "x \<sharp> bn(p \<bullet> \<alpha>')" and "bn(p \<bullet> \<alpha>') \<sharp>* X" by simp+

      note S PeqP' \<open>distinctPerm p\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* C'\<close>
      moreover from FrP' \<open>P'' = \<lparr>\<nu>x\<rparr>P'''\<close> have "extractFrame P'' = \<langle>(x#A\<^sub>P'), \<Psi>\<^sub>P'\<rangle>" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* P'''\<close> \<open>P'' = \<lparr>\<nu>x\<rparr>P'''\<close> \<open>x \<sharp> A\<^sub>P'\<close> have "(x#A\<^sub>P') \<sharp>* P''" by(simp add: abs_fresh)
      moreover from \<open>A\<^sub>P' \<sharp>* \<alpha>'\<close> \<open>A\<^sub>P' \<sharp>* C\<close>  \<open>x \<sharp> \<alpha>'\<close> \<open>x \<sharp> C\<close> have "(x#A\<^sub>P') \<sharp>* \<alpha>'"  and "(x#A\<^sub>P') \<sharp>* C" by simp+
      moreover note \<open>bn(p \<bullet> \<alpha>') \<sharp>* \<alpha>'\<close>
      moreover from \<open>bn(p \<bullet> \<alpha>') \<sharp>* P'''\<close> \<open>P'' = \<lparr>\<nu>x\<rparr>P'''\<close> \<open>x \<sharp> bn(p \<bullet> \<alpha>')\<close> have "bn(p \<bullet> \<alpha>') \<sharp>* P''" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* \<alpha>'\<close> \<open>x \<sharp> \<alpha>'\<close> have "(x#A\<^sub>P') \<sharp>* \<alpha>'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>')\<close> \<open>x \<sharp> \<alpha>'\<close> S \<open>x \<sharp> bn(p \<bullet> \<alpha>')\<close> have "(x#A\<^sub>P') \<sharp>* (p \<bullet> \<alpha>')" 
        by(simp add: subjectEqvt[symmetric] bnEqvt[symmetric] okjectEqvt[symmetric] freshChainSimps)
      moreover from \<open>A\<^sub>P' \<sharp>* X\<close> \<open>x \<sharp> X\<close> have "(x#A\<^sub>P') \<sharp>* X" by simp+
      moreover from \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>x \<sharp> Y\<close> have "(x#A\<^sub>P') \<sharp>* Y" by simp+
      moreover from \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>x \<sharp> Z\<close> have "(x#A\<^sub>P') \<sharp>* Z" by simp+
      moreover note \<open>bn(p \<bullet> \<alpha>') \<sharp>* X\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* Y\<close> \<open>bn(p \<bullet> \<alpha>') \<sharp>* Z\<close>
      moreover from \<open>distinct A\<^sub>P'\<close> \<open>x \<sharp> A\<^sub>P'\<close> have "distinct(x#A\<^sub>P')" by simp
      ultimately show ?case by(rule_tac cScope)
    next
      case(cBang \<Psi> P A\<^sub>P \<Psi>\<^sub>P C C' \<alpha> P' X Y Z)
      then obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))"
                                  and FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                  and PeqP': "(p \<bullet> (\<Psi>\<^sub>P \<otimes> \<one>)) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                                  and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)"
                                  and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
                                  and "distinctPerm p" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'"
                                  and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* X" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Y" and "(bn(p \<bullet> \<alpha>)) \<sharp>* Z"
        by(rule_tac cBang) (assumption | simp (no_asm_use))+
      moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "(p \<bullet> \<Psi>\<^sub>P) \<simeq> (p \<bullet> \<one>)"
        by(simp add: AssertionStatEqClosed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<simeq> \<one>" by(simp add: permBottom)
      with PeqP' have "(\<one> \<otimes> \<Psi>') \<simeq> \<Psi>\<^sub>P'"
        by(simp add: eqvts permBottom) (metis Identity AssertionStatEqTrans composition' Commutativity Associativity AssertionStatEqSym)
      ultimately show ?case using cBang
        apply(rule_tac cBang(18)) by(assumption | simp)+ 
    qed
    
    with A have ?thesis by blast
  }
  moreover have "bn \<alpha> \<sharp>* ([]::name list)" and "bn \<alpha> \<sharp>* ([]::'b list)" and "bn \<alpha> \<sharp>* ([]::('a, 'b, 'c) psi list)"
           and  "A\<^sub>P \<sharp>* ([]::name list)" and "A\<^sub>P \<sharp>* ([]::'b list)" and "A\<^sub>P \<sharp>* ([]::('a, 'b, 'c) psi list)" 
    by simp+
  ultimately show ?thesis by blast
qed

lemma expandTauFrame:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b,'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"

  obtains \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>"  and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "distinct A\<^sub>P'"
proof -
  assume A: "\<And>A\<^sub>P' \<Psi>\<^sub>P' \<Psi>'.
        \<lbrakk>extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>; \<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'; A\<^sub>P' \<sharp>* C; A\<^sub>P' \<sharp>* P'; distinct A\<^sub>P'\<rbrakk>
        \<Longrightarrow> thesis"

  from \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec>P'\<close> \<open>A\<^sub>P \<sharp>* P\<close> have "A\<^sub>P \<sharp>* P'" by(rule tauFreshChainDerivative)

  {
    fix X :: "name list"
    and Y :: "'b list"
    and Z :: "('a, 'b, 'c) psi list"

    assume "A\<^sub>P \<sharp>* X"
    and    "A\<^sub>P \<sharp>* Y"
    and    "A\<^sub>P \<sharp>* Z"
    
    with assms \<open>A\<^sub>P \<sharp>* P'\<close> obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C"
                                               and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" and "distinct A\<^sub>P'"
    proof(nominal_induct avoiding: C X Y Z arbitrary: thesis rule: tauFrameInduct)
      case(cAlpha \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P p C X Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
        by metis

      have S: "set p \<subseteq> set A\<^sub>P \<times> set(p \<bullet> A\<^sub>P)" by fact

      from FrP' have "(p \<bullet> extractFrame P') = p \<bullet> \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" by simp
      with \<open>A\<^sub>P \<sharp>* P'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> S have "extractFrame P' = \<langle>(p \<bullet> A\<^sub>P'), (p \<bullet> \<Psi>\<^sub>P')\<rangle>" by(simp add: eqvts)
      moreover from \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close> have "(p \<bullet> (\<Psi>\<^sub>P \<otimes> \<Psi>')) \<simeq> (p \<bullet> \<Psi>\<^sub>P')" by(rule AssertionStatEqClosed)
      hence "(p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>') \<simeq> (p \<bullet> \<Psi>\<^sub>P')" by(simp add: eqvts)
      moreover from \<open>A\<^sub>P' \<sharp>* C\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> C)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* C\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* C\<close> S have "(p \<bullet> A\<^sub>P') \<sharp>* C" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* P'\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> P')" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* P'\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* P'\<close> S have "(p \<bullet> A\<^sub>P') \<sharp>* P'" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* X\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> X)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* X\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* X\<close> S have "(p \<bullet> A\<^sub>P') \<sharp>* X" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Y\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Y)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* Y\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Y\<close> S have "(p \<bullet> A\<^sub>P') \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Z\<close> have "(p \<bullet> A\<^sub>P') \<sharp>* (p \<bullet> Z)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>P \<sharp>* Z\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* Z\<close> S have "(p \<bullet> A\<^sub>P') \<sharp>* Z" by simp
      moreover from \<open>distinct A\<^sub>P'\<close> have "distinct(p \<bullet> A\<^sub>P')" by simp
      ultimately show ?case by(rule cAlpha)
    next
      case(cCase \<Psi> P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P C B Y Z thesis)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'"
                                and "A\<^sub>P' \<sharp>* B" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
        by(rule_tac cCase) (assumption | simp (no_asm_use))+
      with \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close> have "\<one> \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
        by(metis Identity AssertionStatEqTrans composition' Commutativity Associativity AssertionStatEqSym)
      thus ?case using FrP' \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>P' \<sharp>* B\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>distinct A\<^sub>P'\<close> using cCase
        by force
    next
      case(cPar1 \<Psi> \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P C X Y Z)
      moreover from \<open>A\<^sub>P \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Z\<close>
      have "A\<^sub>P \<sharp>* (X@A\<^sub>Q)" and  "A\<^sub>P \<sharp>* (\<Psi>\<^sub>Q#Y)" and  "A\<^sub>P \<sharp>* (Q#Z)"
        by simp+
      ultimately obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'"
                                      and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* C" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" 
                                      and "A\<^sub>P' \<sharp>* (X@A\<^sub>Q)" and "A\<^sub>P' \<sharp>* (\<Psi>\<^sub>Q#Y)" and "A\<^sub>P' \<sharp>* (Q#Z)"
        by metis

      hence "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P' \<sharp>* Q" and "A\<^sub>P' \<sharp>* Z"
        by simp+

      from \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> FrP' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'" by(force dest: extractFrameFreshChain)
      with \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> FrP'
      have "extractFrame(P' \<parallel> Q) = \<langle>(A\<^sub>P'@A\<^sub>Q), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q\<rangle>" by simp

      moreover from \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close>have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q" 
        by(metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)

      moreover from \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* C\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* C" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* (P' \<parallel> Q)" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* X\<close> \<open>A\<^sub>Q \<sharp>* X\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* X" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* Y\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>A\<^sub>Q \<sharp>* Z\<close> have "(A\<^sub>P'@A\<^sub>Q) \<sharp>* Z" by simp
      moreover from \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>distinct A\<^sub>P'\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(A\<^sub>P'@A\<^sub>Q)" by simp
      ultimately show ?case by(rule cPar1)
    next
      case(cPar2 \<Psi> \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q C X Y Z)
      moreover from \<open>A\<^sub>Q \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Z\<close>
      have "A\<^sub>Q \<sharp>* (X@A\<^sub>P)" and  "A\<^sub>Q \<sharp>* (\<Psi>\<^sub>P#Y)" and  "A\<^sub>Q \<sharp>* (P#Z)"
        by(simp add: freshChainSimps)+
      ultimately obtain \<Psi>' A\<^sub>Q' \<Psi>\<^sub>Q' where FrQ': "extractFrame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "distinct A\<^sub>Q'"
                                       and "\<Psi>\<^sub>Q \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>Q'"and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* Q'" 
                                       and "A\<^sub>Q' \<sharp>* (X@A\<^sub>P)" and "A\<^sub>Q' \<sharp>* (\<Psi>\<^sub>P#Y)" and "A\<^sub>Q' \<sharp>* (P#Z)"
        by metis

      hence "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* A\<^sub>P" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* Z"
        by simp+

      from \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> FrQ' have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q'" by(force dest: extractFrameFreshChain)
      with \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> FrQ'
      have "extractFrame(P \<parallel> Q') = \<langle>(A\<^sub>P@A\<^sub>Q'), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'\<rangle>" by simp

      moreover from \<open>\<Psi>\<^sub>Q \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>Q'\<close>have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q'" 
        by(metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)
      moreover from \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>Q' \<sharp>* C\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* C" by simp
      moreover from \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>Q' \<sharp>* Q'\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* (P \<parallel> Q')" by simp
      moreover from \<open>A\<^sub>P \<sharp>* X\<close> \<open>A\<^sub>Q' \<sharp>* X\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* X" by simp
      moreover from \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>Q' \<sharp>* Y\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from \<open>A\<^sub>P \<sharp>* Z\<close> \<open>A\<^sub>Q' \<sharp>* Z\<close> have "(A\<^sub>P@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from \<open>A\<^sub>Q' \<sharp>* A\<^sub>P\<close> \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q'\<close> have "distinct(A\<^sub>P@A\<^sub>Q')" by simp
      ultimately show ?case by(rule cPar2)
    next
      case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q C X Y Z)
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" and QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact+
      from PTrans \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* N\<close> \<open>A\<^sub>P \<sharp>* M\<close>
           \<open>A\<^sub>P \<sharp>* Q'\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>P \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* Z\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
      obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and PeqP': "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* Q'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "distinct A\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* P'"
        by(rule_tac C="(Q', C, X, Y, Z, A\<^sub>Q, xvec)" and C'="(Q', C, X, Y, Z, A\<^sub>Q, xvec)" in expandNonTauFrame) auto
      moreover from QTrans  have "distinct xvec" by(auto dest: boundOutputDistinct)
      from QTrans \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
           \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P' \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* N\<close> 
           \<open>A\<^sub>Q \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* X\<close> \<open>A\<^sub>Q \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* Z\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* C\<close> \<open>xvec \<sharp>* X\<close> \<open>xvec \<sharp>* Y\<close> \<open>xvec \<sharp>* Z\<close>
      obtain p \<Psi>'' A\<^sub>Q' \<Psi>\<^sub>Q' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and QeqQ': "(p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>Q'" and FrQ': "extractFrame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>"
                             and "A\<^sub>Q' \<sharp>* A\<^sub>P'" and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* P" and "A\<^sub>Q' \<sharp>* N" and "distinct A\<^sub>Q'"
                             and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* X" and "(p \<bullet> xvec) \<sharp>* Y" and "(p \<bullet> xvec) \<sharp>* P"
                             and "(p \<bullet> xvec) \<sharp>* Z" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q'"and "(p \<bullet> xvec) \<sharp>* Q'"
                             and "distinctPerm p" and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* Q'"
        by(rule_tac C="(P, C, X, Y, Z, A\<^sub>P', \<Psi>\<^sub>P)" and C'="(P, C, X, Y, Z, A\<^sub>P', \<Psi>\<^sub>P)" in expandNonTauFrame) (assumption | simp)+

      from PTrans \<open>A\<^sub>Q' \<sharp>* P\<close> \<open>A\<^sub>Q' \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> 
      have "A\<^sub>Q' \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* P'" by(force dest: inputFreshChainDerivative)+
      with FrP' \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'" by(force dest: extractFrameFreshChain)+
      from FrQ' \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>P' \<sharp>* Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q'\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> have "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'"
        by(force dest: extractFrameFreshChain)+
      
      have "extractFrame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q'), (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')\<rangle>"
      proof -
        from FrP' FrQ' \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'\<close> have "extractFrame(P' \<parallel> Q') = \<langle>(A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
          by simp
        hence "extractFrame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>(xvec@A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
          by(induct xvec) auto
        moreover from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'\<close> S 
        have "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> \<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert(\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q')))"
          by(rule_tac frameChainAlpha) (auto simp add: fresh_star_def frameResChainFresh)
        hence "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert((p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q'))))"
          using \<open>A\<^sub>P' \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q'\<close> S
          by(fastforce simp add: eqvts)
        ultimately show ?thesis
          by(simp add: frameChainAppend)
      qed
          
      moreover have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> ((p \<bullet> \<Psi>') \<otimes> (p \<bullet> \<Psi>'')) \<simeq> (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')"
      proof -
        have "(\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> (\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> ((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'')"
          by(metis Associativity Commutativity Composition AssertionStatEqTrans)
        moreover from PeqP' QeqQ' have "(\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> ((p \<bullet> \<Psi>\<^sub>Q) \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
          by(metis Associativity Commutativity Composition AssertionStatEqTrans)
        ultimately have "(\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
          by(metis AssertionStatEqTrans)
        hence "(p \<bullet> ((\<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>Q)) \<otimes> (\<Psi>' \<otimes> \<Psi>''))) \<simeq> (p \<bullet> (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))"
          by(rule AssertionStatEqClosed)
        with \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P\<close> S \<open>distinctPerm p\<close> show ?thesis
          by(simp add: eqvts)
      qed

      moreover from \<open>(p \<bullet> xvec) \<sharp>* C\<close> \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>Q' \<sharp>* C\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* C" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* X\<close> \<open>A\<^sub>P' \<sharp>* X\<close> \<open>A\<^sub>Q' \<sharp>* X\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* X" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* Y\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>Q' \<sharp>* Y\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* Z\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>A\<^sub>Q' \<sharp>* Z\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* Q' \<close>\<open>A\<^sub>Q' \<sharp>* P'\<close> \<open>A\<^sub>Q' \<sharp>* Q'\<close>
      have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))" by(auto simp add: resChainFresh fresh_star_def)
      moreover from \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>distinct xvec\<close> \<open>distinct A\<^sub>P'\<close> \<open>distinct A\<^sub>Q'\<close>
       have "distinct((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q')"
         by auto (simp add: name_list_supp fresh_star_def fresh_def)+

      ultimately show ?case using cComm1
        by metis
    next
      case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q C X Y Z)
      have PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by fact+
      from PTrans have "distinct xvec" by(auto dest: boundOutputDistinct)
      from PTrans \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>distinct xvec\<close> \<open>xvec \<sharp>* M\<close>
                  \<open>A\<^sub>P \<sharp>* C\<close> \<open>A\<^sub>P \<sharp>* X\<close> \<open>A\<^sub>P \<sharp>* Y\<close> \<open>A\<^sub>P \<sharp>* Z\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* N\<close>
                  \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* C\<close> \<open>xvec \<sharp>* X\<close> \<open>xvec \<sharp>* Y\<close> \<open>xvec \<sharp>* Z\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close>
      obtain p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                           and FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and PeqP': "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinct A\<^sub>P'"
                           and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* X" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* N" and "A\<^sub>P' \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* Q"
                           and "A\<^sub>P' \<sharp>* Z" and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* xvec" and "A\<^sub>P' \<sharp>* P'" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q"
                           and "(p \<bullet> xvec) \<sharp>* A\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* C" and "(p \<bullet> xvec) \<sharp>* X" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" 
                           and "(p \<bullet> xvec) \<sharp>* Y" and "(p \<bullet> xvec) \<sharp>* Z" and "(p \<bullet> xvec) \<sharp>* P'" and "distinctPerm p"
        by(rule_tac C="(C, X, Y, Z, A\<^sub>Q, Q, \<Psi>\<^sub>Q)" and C'="(C, X, Y, Z, A\<^sub>Q, Q, \<Psi>\<^sub>Q)" in expandNonTauFrame) (assumption | simp)+

      from QTrans \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close>
           \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* C\<close> \<open>A\<^sub>Q \<sharp>* X\<close> \<open>A\<^sub>Q \<sharp>* Y\<close> \<open>A\<^sub>Q \<sharp>* Z\<close> \<open>A\<^sub>Q \<sharp>* N\<close>  \<open>A\<^sub>Q \<sharp>* K\<close> 
      obtain \<Psi>'' A\<^sub>Q' \<Psi>\<^sub>Q' where QeqQ': "\<Psi>\<^sub>Q \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>Q'" and FrQ': "extractFrame Q' = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "distinct A\<^sub>Q'"
                             and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* Q'" and "A\<^sub>Q' \<sharp>* xvec" and "A\<^sub>Q' \<sharp>* P'" and "A\<^sub>Q' \<sharp>* (p \<bullet> xvec)"
                             and "A\<^sub>Q' \<sharp>* A\<^sub>P'" and "A\<^sub>Q' \<sharp>* C" and "A\<^sub>Q' \<sharp>* X" and "A\<^sub>Q' \<sharp>* Y" and "A\<^sub>Q' \<sharp>* Z" and "A\<^sub>Q' \<sharp>* P"
        by(rule_tac C="(P, C, P', X, Y, Z, A\<^sub>P', xvec, (p \<bullet> xvec), \<Psi>\<^sub>P)" and C'="(P, C, P', X, Y, Z, A\<^sub>P', xvec, (p \<bullet> xvec), \<Psi>\<^sub>P)" in expandNonTauFrame) (assumption | simp)+

      from QTrans \<open>A\<^sub>P' \<sharp>* Q\<close> \<open>A\<^sub>P' \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> 
      have "A\<^sub>P' \<sharp>* Q'" and "(p \<bullet> xvec) \<sharp>* Q'" by(force dest: inputFreshChainDerivative)+
      with FrQ' \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* (p \<bullet> xvec)\<close> have "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'" by(force dest: extractFrameFreshChain)+
      from FrP' \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* P'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* P'\<close> have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'"
        by(force dest: extractFrameFreshChain)+

      have "extractFrame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q'), (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')\<rangle>"
      proof -
        from FrP' FrQ' \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>P'\<close> have "extractFrame(P' \<parallel> Q') = \<langle>(A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
          by simp
        hence "extractFrame(\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) = \<langle>(xvec@A\<^sub>P'@A\<^sub>Q'), \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'\<rangle>"
          by(induct xvec) auto
        moreover from \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q'\<close> S 
        have "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> \<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert(\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q')))"
          by(rule_tac frameChainAlpha) (auto simp add: fresh_star_def frameResChainFresh)
        hence "\<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))) = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(\<lparr>\<nu>*(A\<^sub>P'@A\<^sub>Q')\<rparr>(FAssert((p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q'))))"
          using \<open>A\<^sub>P' \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open>A\<^sub>Q' \<sharp>* xvec\<close> \<open>A\<^sub>Q' \<sharp>* (p \<bullet> xvec)\<close> S
          by(fastforce simp add: eqvts)
        ultimately show ?thesis
          by(simp add: frameChainAppend)
      qed
          
      moreover have "(\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> ((p \<bullet> \<Psi>') \<otimes> (p \<bullet> \<Psi>'')) \<simeq> (p \<bullet> \<Psi>\<^sub>P') \<otimes> (p \<bullet> \<Psi>\<^sub>Q')"
      proof -
        have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>'')"
          by(metis Associativity Commutativity Composition AssertionStatEqTrans)
        moreover from PeqP' QeqQ' have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>') \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
          by(metis Associativity Commutativity Composition AssertionStatEqTrans)
        ultimately have "((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'') \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'"
          by(metis AssertionStatEqTrans)
        hence "(p \<bullet> ((p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q) \<otimes> (\<Psi>' \<otimes> \<Psi>'')) \<simeq> (p \<bullet> (\<Psi>\<^sub>P' \<otimes> \<Psi>\<^sub>Q'))"
          by(rule AssertionStatEqClosed)
        with \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> S \<open>distinctPerm p\<close> show ?thesis
          by(simp add: eqvts)
      qed

      moreover from \<open>(p \<bullet> xvec) \<sharp>* C\<close> \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>Q' \<sharp>* C\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* C" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* X\<close> \<open>A\<^sub>P' \<sharp>* X\<close> \<open>A\<^sub>Q' \<sharp>* X\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* X" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* Y\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>Q' \<sharp>* Y\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Y" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* Z\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>A\<^sub>Q' \<sharp>* Z\<close> have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* Z" by simp
      moreover from \<open>(p \<bullet> xvec) \<sharp>* P'\<close> \<open>(p \<bullet> xvec) \<sharp>* Q'\<close> \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* Q' \<close>\<open>A\<^sub>Q' \<sharp>* P'\<close> \<open>A\<^sub>Q' \<sharp>* Q'\<close>
      have "((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q') \<sharp>* (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))" by(auto simp add: resChainFresh fresh_star_def)
      moreover from \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P'\<close> \<open> A\<^sub>Q' \<sharp>* (p \<bullet> xvec)\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>P'\<close> \<open>distinct xvec\<close> \<open>distinct A\<^sub>P'\<close> \<open>distinct A\<^sub>Q'\<close>
       have "distinct((p \<bullet> xvec)@A\<^sub>P'@A\<^sub>Q')"
         by auto (simp add: name_list_supp fresh_star_def fresh_def)+

      ultimately show ?case using cComm2 by metis
    next
      case(cScope \<Psi> P P' x A\<^sub>P \<Psi>\<^sub>P C X Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "distinct A\<^sub>P'"
                                and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'"
                                and "A\<^sub>P' \<sharp>* (x#X)" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z" 
        by(rule_tac cScope(4)[where ba="x#X"]) auto
      from \<open>A\<^sub>P' \<sharp>* (x#X)\<close> have "x \<sharp> A\<^sub>P'" and "A\<^sub>P' \<sharp>* X" by simp+
      moreover from FrP' have "extractFrame(\<lparr>\<nu>x\<rparr>P') = \<langle>(x#A\<^sub>P'), \<Psi>\<^sub>P'\<rangle>" by simp
      moreover note \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close>
      moreover from \<open>x \<sharp> C\<close> \<open>A\<^sub>P' \<sharp>* C\<close> have "(x#A\<^sub>P') \<sharp>* C" by simp
      moreover from  \<open>A\<^sub>P' \<sharp>* P'\<close> have "(x#A\<^sub>P') \<sharp>* (\<lparr>\<nu>x\<rparr>P')" by(simp add: abs_fresh fresh_star_def)
      moreover from \<open>x \<sharp> X\<close> \<open>A\<^sub>P' \<sharp>* X\<close> have "(x#A\<^sub>P') \<sharp>* X" by simp
      moreover from \<open>x \<sharp> Y\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> have "(x#A\<^sub>P') \<sharp>* Y" by simp
      moreover from \<open>x \<sharp> Z\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> have "(x#A\<^sub>P') \<sharp>* Z" by simp
      moreover from \<open>x \<sharp> A\<^sub>P'\<close> \<open>distinct A\<^sub>P'\<close> have "distinct(x#A\<^sub>P')" by simp
      ultimately show ?case by(rule_tac cScope)
    next
      case(cBang \<Psi> P P' A\<^sub>P \<Psi>\<^sub>P C B Y Z)
      then obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" 
                                and "(\<Psi>\<^sub>P \<otimes> \<one>) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* C" and "A\<^sub>P' \<sharp>* P'" and "distinct A\<^sub>P'"
                                and "A\<^sub>P' \<sharp>* B" and "A\<^sub>P' \<sharp>* Y" and "A\<^sub>P' \<sharp>* Z"
        by(rule_tac cBang) (assumption | simp)+
      with \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>(\<Psi>\<^sub>P \<otimes> \<one>) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close> have "\<one> \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
        by(metis Identity AssertionStatEqTrans composition' Commutativity Associativity AssertionStatEqSym)
      thus ?case using FrP' \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* C\<close> \<open>A\<^sub>P' \<sharp>* B\<close> \<open>A\<^sub>P' \<sharp>* Y\<close> \<open>A\<^sub>P' \<sharp>* Z\<close> \<open>distinct A\<^sub>P'\<close>
        by(rule_tac cBang)
    qed
    with A have ?thesis by simp
  }
  moreover have "A\<^sub>P \<sharp>* ([]::name list)" and "A\<^sub>P \<sharp>* ([]::'b list)" and "A\<^sub>P \<sharp>* ([]::('a, 'b, 'c) psi list)" by simp+
  ultimately show ?thesis by blast
qed

lemma expandFrame:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b
  and   C    :: "'d::fs_name"
  and   C'   :: "'e::fs_name"
  
  assumes Trans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"
  and     "A\<^sub>P \<sharp>* C'"
  and     "bn \<alpha> \<sharp>* P"
  and     "bn \<alpha> \<sharp>* C'"

  obtains p \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "distinctPerm p" and
                              "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<alpha>" and "A\<^sub>P' \<sharp>* (p \<bullet> \<alpha>)" and
                              "A\<^sub>P' \<sharp>* C" and "(bn(p \<bullet> \<alpha>)) \<sharp>* C'" and "(bn(p \<bullet> \<alpha>)) \<sharp>* \<alpha>" and "(bn(p \<bullet> \<alpha>)) \<sharp>* P'" and "distinct A\<^sub>P'"
using assms
apply(cases "\<alpha>=\<tau>")
by(auto intro: expandTauFrame[where C=C] expandNonTauFrame[where C=C and C'=C'])

abbreviation
  frameImpJudge ("_ \<hookrightarrow>\<^sub>F _" [80, 80] 80)
  where "F \<hookrightarrow>\<^sub>F G \<equiv> FrameStatImp F G"

lemma FrameStatEqImpCompose:
  fixes F :: "'b frame"
  and   G :: "'b frame"
  and   H :: "'b frame"
  and   I :: "'b frame"

  assumes "F \<simeq>\<^sub>F G"
  and     "G \<hookrightarrow>\<^sub>F H"
  and     "H \<simeq>\<^sub>F I"

  shows "F \<hookrightarrow>\<^sub>F I"
using assms
by(auto simp add: FrameStatEq_def) (blast intro: FrameStatImpTrans)

lemma transferNonTauFrame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct(bn \<alpha>)"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>F \<sharp>* subject \<alpha>"
  and     "A\<^sub>G \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"
  and     "\<alpha> \<noteq> \<tau>"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
using assms
proof(nominal_induct \<Psi>\<^sub>F P Rs=="\<alpha> \<prec> P'" A\<^sub>P \<Psi>\<^sub>P avoiding: \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G rule: semanticsFrameInduct)
  case(cAlpha \<Psi>\<^sub>F P A\<^sub>P \<Psi>\<^sub>P p \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>\<close>
  have "(p \<bullet> (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>)) \<hookrightarrow>\<^sub>F (p \<bullet> (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>))"
    by(rule FrameStatImpClosed)
  with \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>G\<close>
    \<open>distinctPerm p\<close> \<open>set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  with cAlpha show ?case by force
next
  case(cInput \<Psi>\<^sub>F M K xvec N Tvec P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from cInput have "A\<^sub>F \<sharp>* K" and "A\<^sub>G \<sharp>* K" by(auto simp add: residualInject)

  from \<open>A\<^sub>F \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)\<close> \<open>A\<^sub>G \<sharp>* (M\<lparr>\<lambda>*xvec N\<rparr>.P)\<close> have "A\<^sub>F \<sharp>* M" and "A\<^sub>G \<sharp>* M" by simp+
  from \<open>\<Psi>\<^sub>F \<turnstile> M \<leftrightarrow> K\<close>
  have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity AssertionStatEqSym)
  with \<open>A\<^sub>F \<sharp>* M\<close> \<open>A\<^sub>F \<sharp>* K\<close>
  have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(force intro: frameImpI)
  with \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(simp add: FrameStatEq_def FrameStatImp_def)
  with \<open>A\<^sub>G \<sharp>* M\<close> \<open>A\<^sub>G \<sharp>* K\<close>
  have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" by(force dest: frameImpE)
  hence "\<Psi>\<^sub>G \<turnstile> M \<leftrightarrow> K" by(blast intro: statEqEnt Identity)
  thus ?case using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close> using cInput Input
    by(force simp add: residualInject)
next
  case(cOutput \<Psi>\<^sub>F M K N P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from cOutput have "A\<^sub>F \<sharp>* K" and "A\<^sub>G \<sharp>* K" by(auto simp add: residualInject)

  from \<open>A\<^sub>F \<sharp>* (M\<langle>N\<rangle>.P)\<close> \<open>A\<^sub>G \<sharp>* (M\<langle>N\<rangle>.P)\<close> have "A\<^sub>F \<sharp>* M" and "A\<^sub>G \<sharp>* M" by simp+
  from \<open>\<Psi>\<^sub>F \<turnstile> M \<leftrightarrow> K\<close>
  have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> M \<leftrightarrow> K"
    by(blast intro: statEqEnt Identity AssertionStatEqSym)
  with \<open>A\<^sub>F \<sharp>* M\<close> \<open>A\<^sub>F \<sharp>* K\<close>
  have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(force intro: frameImpI)
  with \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> K"
    by(simp add: FrameStatImp_def) 
  with \<open>A\<^sub>G \<sharp>* M\<close> \<open>A\<^sub>G \<sharp>* K\<close>
  have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" by(force dest: frameImpE)
  hence "\<Psi>\<^sub>G \<turnstile> M \<leftrightarrow> K" by(blast intro: statEqEnt Identity) 
  thus ?case using cOutput Output by(force simp add: residualInject) 
next
  case(cCase \<Psi>\<^sub>F P \<phi> Cs A\<^sub>P \<Psi>\<^sub>P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans AssertionStatEqSym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule FrameStatEqImpCompose)
  with cCase have "\<Psi>\<^sub>G \<rhd> P \<longmapsto> \<alpha> \<prec> P'" by(fastforce dest: memFreshChain)
  moreover note \<open>(\<phi>, P) mem Cs\<close> 
  moreover from \<open>A\<^sub>F \<sharp>* (Cases Cs)\<close>\<open>A\<^sub>G \<sharp>* (Cases Cs)\<close> \<open>(\<phi>, P) mem Cs\<close> have "A\<^sub>F \<sharp>* \<phi>" and "A\<^sub>G \<sharp>* \<phi>"
    by(auto dest: memFreshChain)
  from \<open>\<Psi>\<^sub>F \<turnstile> \<phi>\<close> have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: statEqEnt Identity AssertionStatEqSym)
  with \<open>A\<^sub>F \<sharp>* \<phi>\<close> have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frameImpI)
  with \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close> have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
    by(simp add: FrameStatImp_def)
  with \<open>A\<^sub>G \<sharp>* \<phi>\<close> have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> \<phi>" by(force dest: frameImpE)
  hence "\<Psi>\<^sub>G \<turnstile> \<phi>" by(blast intro: statEqEnt Identity)
  ultimately show ?case using \<open>guarded P\<close> cCase Case by(force intro: residualInject)
next
  case(cPar1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P \<alpha> P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P \<alpha>' PQ' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>\<close>
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
    by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule FrameStatEqImpCompose)
  moreover from \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  moreover note \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>F \<sharp>* subject \<alpha>'\<close> \<open>A\<^sub>G \<sharp>* subject \<alpha>'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close>
  moreover from \<open>\<alpha> \<prec> P' \<parallel> Q = \<alpha>' \<prec> PQ'\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> 
  obtain p P'' where "\<alpha> \<prec> P' = \<alpha>' \<prec> P''" and "set p \<subseteq> set(bn \<alpha>') \<times> set(bn \<alpha>)" and "PQ' = P'' \<parallel> (p \<bullet> Q)"
    apply(drule_tac sym)
    by(rule_tac actionPar1Dest) (assumption | simp | blast dest: sym)+
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'" using \<open>\<alpha>' \<noteq> \<tau>\<close> by(force intro: cPar1)
  thus ?case using FrQ \<open>(bn \<alpha>) \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> using cPar1
    by(metis Par1)
next
  case(cPar2 \<Psi>\<^sub>F \<Psi>\<^sub>P Q \<alpha> Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q \<alpha>' PQ' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity frameResChainPres frameNilStatEq)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>\<close>
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
    by(metis Associativity AssertionStatEqSym frameResChainPres frameNilStatEq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule FrameStatEqImpCompose)
  moreover from \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)+
  moreover note \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>F \<sharp>* subject \<alpha>'\<close> \<open>A\<^sub>G \<sharp>* subject \<alpha>'\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close>
  moreover from \<open>\<alpha> \<prec> P \<parallel> Q' = \<alpha>' \<prec> PQ'\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> 
  obtain p Q'' where "\<alpha> \<prec> Q' = \<alpha>' \<prec> Q''" and "set p \<subseteq> set(bn \<alpha>') \<times> set(bn \<alpha>)" and "PQ' = (p \<bullet> P) \<parallel> Q''"
    apply(drule_tac sym)
    by(rule_tac actionPar2Dest) (assumption | simp | blast dest: sym)+
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" using \<open>\<alpha>' \<noteq> \<tau>\<close> by(force intro: cPar2)
  thus ?case using FrP \<open>(bn \<alpha>) \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> using cPar2
    by(metis Par2)
next
  case cComm1
  thus ?case by(simp add: residualInject)
next
  case cComm2
  thus ?case by(simp add: residualInject)
next
  case(cOpen \<Psi>\<^sub>F P M xvec yvec N P' x A\<^sub>P \<Psi>\<^sub>P \<alpha> P'' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>M\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> P''\<close> \<open>distinct(bn \<alpha>)\<close>
  obtain xvec' x' yvec' N' where "M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P' =  M\<lparr>\<nu>*(xvec'@yvec')\<rparr>\<langle>([(x, x')] \<bullet> N')\<rangle> \<prec> ([(x, x')] \<bullet> P'')" 
                             and "\<alpha> = M\<lparr>\<nu>*(xvec'@x'#yvec')\<rparr>\<langle>N'\<rangle>"
    apply(cases rule: actionCases[where \<alpha>=\<alpha>])
    apply(auto simp add: residualInject)
    apply(rule boundOutputOpenDest) by assumption auto

  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" using cOpen
    by(rule_tac cOpen) (assumption | simp)+
  with \<open>x \<in> supp N\<close> \<open>x \<sharp> \<Psi>\<^sub>G\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close>
  have "\<Psi>\<^sub>G \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" 
    by(rule_tac Open)
  thus ?case using \<open>\<alpha> = M\<lparr>\<nu>*(xvec'@x'#yvec')\<rparr>\<langle>N'\<rangle>\<close> \<open>M\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>\<langle>N\<rangle> \<prec> P' = \<alpha> \<prec> P''\<close>
    by simp
next
  case(cScope \<Psi>\<^sub>F P \<alpha> P' x A\<^sub>P \<Psi>\<^sub>P \<alpha>' xP \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P' = \<alpha>' \<prec> xP\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> \<alpha>'\<close> obtain P'' where "xP = \<lparr>\<nu>x\<rparr>P''" and "\<alpha> \<prec> P' = \<alpha>' \<prec> P''"
    by(drule_tac sym) (force intro: actionScopeDest)
  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<alpha> \<prec> P'" using cScope by auto
  with \<open>x \<sharp> \<Psi>\<^sub>G\<close> \<open>x \<sharp> \<alpha>'\<close> \<open>\<alpha> \<prec> P' = \<alpha>' \<prec> P''\<close> \<open>xP = \<lparr>\<nu>x\<rparr>P''\<close> show ?case
    by(metis Scope)
next
  case(cBang \<Psi>\<^sub>F P A\<^sub>P \<Psi>\<^sub>P \<alpha> P' \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans AssertionStatEqSym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(rule FrameStatEqImpCompose)
  with cBang have "\<Psi>\<^sub>G \<rhd> P \<parallel> !P \<longmapsto> \<alpha> \<prec> P'" by force
  thus ?case using \<open>guarded P\<close> using cBang by(metis Bang)
qed

lemma transferTauFrame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<tau> \<prec> P'"
using assms
proof(nominal_induct avoiding: \<Psi>\<^sub>G A\<^sub>F A\<^sub>G rule: tauFrameInduct)
  case(cAlpha \<Psi>\<^sub>F P P' A\<^sub>P \<Psi>\<^sub>P p \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>\<close>
  have "(p \<bullet> (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>)) \<hookrightarrow>\<^sub>F (p \<bullet> (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> (p \<bullet> \<Psi>\<^sub>P)\<rangle>))"
    by(rule FrameStatImpClosed)
  with \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>(p \<bullet> A\<^sub>P) \<sharp>* \<Psi>\<^sub>G\<close>
    \<open>distinctPerm p\<close> \<open>set p \<subseteq> set A\<^sub>P \<times> set (p \<bullet> A\<^sub>P)\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  with cAlpha show ?case by blast
next
  case(cCase \<Psi>\<^sub>F P P' \<phi> Cs A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans AssertionStatEqSym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule FrameStatEqImpCompose)
  with cCase have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<tau> \<prec> P'" by(fastforce dest: memFreshChain)
  moreover note \<open>(\<phi>, P) mem Cs\<close> 
  moreover from \<open>A\<^sub>F \<sharp>* (Cases Cs)\<close>\<open>A\<^sub>G \<sharp>* (Cases Cs)\<close> \<open>(\<phi>, P) mem Cs\<close> have "A\<^sub>F \<sharp>* \<phi>" and "A\<^sub>G \<sharp>* \<phi>"
    by(auto dest: memFreshChain)
  from \<open>\<Psi>\<^sub>F \<turnstile> \<phi>\<close> have "\<Psi>\<^sub>F \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: statEqEnt Identity AssertionStatEqSym)
  with \<open>A\<^sub>F \<sharp>* \<phi>\<close> have "(\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frameImpI)
  with \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close> have "(\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
    by(simp add: FrameStatImp_def)
  with \<open>A\<^sub>G \<sharp>* \<phi>\<close> have "\<Psi>\<^sub>G \<otimes> \<one> \<turnstile> \<phi>" by(force dest: frameImpE)
  hence "\<Psi>\<^sub>G \<turnstile> \<phi>" by(blast intro: statEqEnt Identity)
  ultimately show ?case using \<open>guarded P\<close> by(rule Case)
next
  case(cPar1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P P' A\<^sub>Q Q A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have IH: "\<And>\<Psi> A\<^sub>F A\<^sub>G. \<lbrakk>\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>P\<rangle>; A\<^sub>F \<sharp>* P; A\<^sub>G \<sharp>* P;
                           A\<^sub>P \<sharp>* A\<^sub>F; A\<^sub>P \<sharp>* A\<^sub>G; A\<^sub>P \<sharp>* (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q); A\<^sub>P \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
    by fact
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>\<close>
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
    by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    by(rule FrameStatEqImpCompose)
  moreover from \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  moreover note \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close>
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<tau> \<prec> P'" by(rule_tac IH) (assumption | auto)+
  thus ?case using FrQ \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* P\<close>
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi>\<^sub>F \<Psi>\<^sub>P Q Q' A\<^sub>P P A\<^sub>Q \<Psi>\<^sub>Q \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have IH: "\<And>\<Psi> A\<^sub>F A\<^sub>G. \<lbrakk>\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle>; A\<^sub>F \<sharp>* Q; A\<^sub>G \<sharp>* Q;
                           A\<^sub>Q \<sharp>* A\<^sub>F; A\<^sub>Q \<sharp>* A\<^sub>G; A\<^sub>Q \<sharp>* (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P); A\<^sub>Q \<sharp>* \<Psi>\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'"
    by fact
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis Associativity frameResChainPres frameNilStatEq)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>\<close>
  moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
    by(metis Associativity AssertionStatEqSym frameResChainPres frameNilStatEq)
  ultimately have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule FrameStatEqImpCompose)
  moreover from \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)+
  moreover note \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close>
  ultimately have  "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" by(rule_tac IH) (assumption | auto)+
  thus ?case using FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* Q\<close>
    by(rule_tac Par2) auto
next
  case(cComm1 \<Psi>\<^sub>F \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  have FimpG: "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by fact
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  from \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)+
  from \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  from \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close> 
  obtain K' where KeqK': "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>F \<sharp>* K'" and "A\<^sub>G \<sharp>* K'" 
    using \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
    by(rule_tac B="A\<^sub>P@A\<^sub>F@A\<^sub>G" in obtainPrefix) force+
  have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'"
  proof -
    from KeqK' have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> K \<leftrightarrow> K'" by(rule statEqEnt[OF Associativity])
    with \<open>\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K'"
      by(rule chanEqTrans)
    hence "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
      by(metis statEqEnt AssertionStatEqSym Associativity AssertionStatEqTrans compositionSym Commutativity)
    with \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close>
    have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>N\<rparr> \<prec> P'" using \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
      by(force intro: inputRenameSubject)
    moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    proof -
      have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
      moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
        by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
      ultimately show ?thesis using FimpG
        by(rule_tac FrameStatEqImpCompose)
    qed
    ultimately show ?thesis using \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>F \<sharp>* K'\<close>
                                  \<open>A\<^sub>G \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> FrP \<open>distinct A\<^sub>P\<close>
      by(auto intro: transferNonTauFrame)
  qed
  
  moreover from FrP \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>distinct A\<^sub>P\<close>
  obtain M' where MeqM': "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "A\<^sub>Q \<sharp>* M'" and "A\<^sub>F \<sharp>* M'" and "A\<^sub>G \<sharp>* M'"
    using \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close>
    by(rule_tac B="A\<^sub>Q@A\<^sub>F@A\<^sub>G" in obtainPrefix) force+

  have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  proof -
    from MeqM' have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P) \<turnstile> M \<leftrightarrow> M'" by(rule statEqEnt[OF Associativity])
    with \<open>\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P) \<turnstile> K \<leftrightarrow> M'"
      by(blast intro: chanEqTrans chanEqSym compositionSym Commutativity statEqEnt)
    hence "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
      by(blast intro: statEqEnt AssertionStatEqSym Associativity
                      AssertionStatEqTrans compositionSym Commutativity)
    with \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close> 
    have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      by(force intro: outputRenameSubject)
    moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    proof -
      have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by(metis Associativity frameResChainPres frameNilStatEq)
      moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
        by(metis Associativity AssertionStatEqSym frameResChainPres frameNilStatEq)
      ultimately show ?thesis using FimpG
        by(rule_tac FrameStatEqImpCompose)
    qed

    ultimately show ?thesis using \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>F \<sharp>* M'\<close> \<open>A\<^sub>G \<sharp>* M'\<close>
                                  \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> FrQ \<open>distinct A\<^sub>Q\<close> \<open>distinct xvec\<close> 
      by(auto intro: transferNonTauFrame)
  qed

  moreover have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
  proof -
    from MeqM' have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> M"
      by(blast intro: chanEqSym Associativity statEqEnt Commutativity compositionSym)
    moreover from KeqK' have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'"
      by(blast intro: chanEqSym Associativity statEqEnt Commutativity compositionSym)
    ultimately have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'" using \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
      by(blast intro: chanEqSym chanEqTrans)
    thus ?thesis using \<open>A\<^sub>F \<sharp>* M'\<close> \<open>A\<^sub>F \<sharp>* K'\<close> \<open>A\<^sub>G \<sharp>* M'\<close> \<open>A\<^sub>G \<sharp>* K'\<close> FimpG
      apply(auto simp add: FrameStatImp_def)
      apply(erule_tac x="SChanEq' K' M'" in allE)
      by(force intro: frameImpI dest: frameImpE)
  qed

  ultimately show ?case using \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>xvec \<sharp>* P\<close> FrP FrQ
   by(rule_tac Comm1) (assumption | simp)+
next
  case(cComm2 \<Psi>\<^sub>F \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  have FimpG: "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>" by fact
  from \<open>A\<^sub>F \<sharp>* (P \<parallel> Q)\<close> \<open>A\<^sub>G \<sharp>* (P \<parallel> Q)\<close> have "A\<^sub>F \<sharp>* P" and "A\<^sub>G \<sharp>* P" and "A\<^sub>F \<sharp>* Q" and "A\<^sub>G \<sharp>* Q"
    by simp+
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
  from \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)+
  from \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>G \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  from \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close>  
  obtain K' where KeqK': "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'" and "A\<^sub>P \<sharp>* K'" and "A\<^sub>F \<sharp>* K'" and "A\<^sub>G \<sharp>* K'"
    using \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close>
    by(rule_tac B="A\<^sub>P@A\<^sub>F@A\<^sub>G" in obtainPrefix) force+
  have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  proof -
    from KeqK' have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> K \<leftrightarrow> K'" by(rule statEqEnt[OF Associativity])
    with \<open>\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K'"
      by(rule chanEqTrans)
    hence "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K'"
      by(metis statEqEnt AssertionStatEqSym Associativity AssertionStatEqTrans compositionSym Commutativity)
    with \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> FrP \<open>distinct A\<^sub>P\<close> 
    have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" using \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* K'\<close>
      by(force intro: outputRenameSubject)
    moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle>"
    proof -
      have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
      moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P\<rangle> "
        by(metis Associativity Composition AssertionStatEqSym AssertionStatEqTrans Commutativity frameResChainPres frameNilStatEq)
      ultimately show ?thesis using FimpG
        by(rule_tac FrameStatEqImpCompose)
    qed
    ultimately show ?thesis using  \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>F \<sharp>* K'\<close>
                                  \<open>A\<^sub>G \<sharp>* K'\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> FrP \<open>distinct A\<^sub>P\<close>
                                  \<open>distinct xvec\<close>
      by(auto intro: transferNonTauFrame)
  qed

  moreover from FrP \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>distinct A\<^sub>P\<close> 
  obtain M' where MeqM': "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> M'" and "A\<^sub>Q \<sharp>* M'" and "A\<^sub>F \<sharp>* M'" and "A\<^sub>G \<sharp>* M'"
    using \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
    by(rule_tac B="A\<^sub>Q@A\<^sub>F@A\<^sub>G" in obtainPrefix) force+

  have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'"
  proof -
    from MeqM' have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P) \<turnstile> M \<leftrightarrow> M'" by(rule statEqEnt[OF Associativity])
    with \<open>\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi>\<^sub>F \<otimes> (\<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>P) \<turnstile> K \<leftrightarrow> M'"
      by(blast intro: chanEqTrans chanEqSym compositionSym Commutativity statEqEnt)
    hence "(\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> M'"
      by(blast intro: statEqEnt AssertionStatEqSym Associativity
                      AssertionStatEqTrans compositionSym Commutativity)
    with \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> FrQ \<open>distinct A\<^sub>Q\<close> 
    have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M'\<lparr>N\<rparr> \<prec> Q'" using \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      by(force intro: inputRenameSubject)
    moreover have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle>"
    proof -
      have "\<langle>A\<^sub>F, (\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by(metis Associativity frameResChainPres frameNilStatEq)
      moreover have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, (\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q\<rangle> "
        by(metis Associativity AssertionStatEqSym frameResChainPres frameNilStatEq)
      ultimately show ?thesis using FimpG
        by(rule_tac FrameStatEqImpCompose)
    qed

    ultimately show ?thesis using \<open>A\<^sub>F \<sharp>* Q\<close> \<open>A\<^sub>G \<sharp>* Q\<close> \<open>A\<^sub>F \<sharp>* M'\<close> \<open>A\<^sub>G \<sharp>* M'\<close>
                                  \<open>A\<^sub>Q \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> FrQ \<open>distinct A\<^sub>Q\<close> \<open>distinct xvec\<close>
      by(auto intro: transferNonTauFrame)
  qed

  moreover have "\<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'"
  proof -
    from MeqM' have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M' \<leftrightarrow> M"
      by(blast intro: chanEqSym Associativity statEqEnt Commutativity compositionSym)
    moreover from KeqK' have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K \<leftrightarrow> K'"
      by(blast intro: chanEqSym Associativity statEqEnt Commutativity compositionSym)
    ultimately have "\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> K' \<leftrightarrow> M'" using \<open>\<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
      by(blast intro: chanEqSym chanEqTrans)
    thus ?thesis using \<open>A\<^sub>F \<sharp>* M'\<close> \<open>A\<^sub>F \<sharp>* K'\<close> \<open>A\<^sub>G \<sharp>* M'\<close> \<open>A\<^sub>G \<sharp>* K'\<close> FimpG
      apply(auto simp add: FrameStatImp_def)
      apply(erule_tac x="SChanEq' K' M'" in allE)
      by(force intro: frameImpI dest: frameImpE)
  qed

  ultimately show ?case using \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* K'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* M'\<close> \<open>xvec \<sharp>* Q\<close> FrP FrQ
    by(rule_tac Comm2) (assumption | simp)+
next
  case(cScope \<Psi>\<^sub>F P P' x A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  then have "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<tau> \<prec> P'" by auto
  with \<open>x \<sharp> \<Psi>\<^sub>G\<close> show ?case
    by(rule_tac Scope) auto
next
  case(cBang \<Psi>\<^sub>F P P' A\<^sub>P \<Psi>\<^sub>P \<Psi>\<^sub>G A\<^sub>F A\<^sub>G)
  from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans)
  moreover note \<open>\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle>\<close>
  moreover from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(metis frameIntCompositionSym Identity AssertionStatEqTrans AssertionStatEqSym)
  ultimately have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    by(rule FrameStatEqImpCompose)
  with cBang have "\<Psi>\<^sub>G \<rhd> P \<parallel> !P \<longmapsto>\<tau> \<prec> P'" by force
  thus ?case using \<open>guarded P\<close> by(rule Bang)
qed

lemma transferFrame:
  fixes \<Psi>\<^sub>F  :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>F   :: "name list"
  and   A\<^sub>G   :: "name list"
  and   \<Psi>\<^sub>G   :: 'b

  assumes "\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>F \<sharp>* subject \<alpha>"
  and     "A\<^sub>G \<sharp>* subject \<alpha>"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"

  shows "\<Psi>\<^sub>G \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
using assms
proof -
  from \<open>\<Psi>\<^sub>F \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> have "distinct(bn \<alpha>)" by(auto dest: boundOutputDistinct)
  thus ?thesis using assms
    by(cases "\<alpha> = \<tau>") (auto intro: transferNonTauFrame transferTauFrame)
qed

lemma parCasesInputFrame[consumes 7, case_names cPar1 cPar2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> T"
  and     "extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P\<^sub>Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>P\<^sub>Q \<sharp>* P"
  and     "A\<^sub>P\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* M"
  and     rPar1: "\<And>P' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop T"
using Trans
proof(induct rule: parInputCases[of _ _ _ _ _ _ "(A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)"])
  case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
  from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)\<close> have "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, M, A\<^sub>Q, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>Q)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by simp+

  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" 
    by(rule_tac inputPermFrame) auto
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extractFrame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> Aeq have "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extractFrame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> Aeq have "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case using \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> Aeq \<Psi>eq
    by(rule_tac rPar1) (assumption | simp)+
next
  case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
  from \<open>A\<^sub>P \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)\<close> have "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, M, A\<^sub>P, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P)"
    by(rule freshFrame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain) 

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'\<close> S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" 
    by(rule_tac inputPermFrame) auto
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extractFrame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> Aeq have "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extractFrame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> Aeq have "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case using \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> Aeq \<Psi>eq
    by(rule_tac rPar2) (assumption | simp)+
qed

lemma parCasesOutputFrame[consumes 11, case_names cPar1 cPar2]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   T    :: "('a, 'b, 'c) psi"
  and   C    :: "'d::fs_name"

  assumes Trans: "\<Psi> \<rhd> P \<parallel> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> T"
  and     "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* Q"
  and     "xvec \<sharp>* M"
  and     "extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P\<^sub>Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>P\<^sub>Q \<sharp>* P"
  and     "A\<^sub>P\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>P\<^sub>Q \<sharp>* M"
  and     rPar1: "\<And>P' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     rPar2: "\<And>Q' A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q \<Psi>\<^sub>Q. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'; extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>; extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>; 
                                      distinct A\<^sub>P; distinct A\<^sub>Q; A\<^sub>P \<sharp>* \<Psi>; A\<^sub>P \<sharp>* P; A\<^sub>P \<sharp>* Q; A\<^sub>P \<sharp>* M;  A\<^sub>Q \<sharp>* \<Psi>; A\<^sub>Q \<sharp>* P; A\<^sub>Q \<sharp>* Q; A\<^sub>Q \<sharp>* M; 
                                      A\<^sub>P \<sharp>* \<Psi>\<^sub>Q; A\<^sub>Q \<sharp>* \<Psi>\<^sub>P; A\<^sub>P \<sharp>* A\<^sub>Q; A\<^sub>P\<^sub>Q = A\<^sub>P@A\<^sub>Q; \<Psi>\<^sub>P\<^sub>Q = \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rbrakk> \<Longrightarrow> Prop (P \<parallel> Q')"
  shows "Prop T"
using Trans \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close>
proof(induct rule: parOutputCases[of _ _ _ _ _ _ _ "(A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)"])
  case(cPar1 P' A\<^sub>Q \<Psi>\<^sub>Q)
  from \<open>A\<^sub>Q \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)\<close> have "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "distinct A\<^sub>P"
                           "A\<^sub>P \<sharp>* (P, Q, \<Psi>, M, A\<^sub>Q, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>Q)"
    by(rule freshFrame)
  hence "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* Q" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by simp+

  have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact

  from \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> FrP have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by(force dest: extractFrameFreshChain)

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q)) \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" 
    by(rule_tac outputPermFrame) (assumption | simp)+

  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>Q) \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extractFrame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> Aeq have "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extractFrame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> Aeq have "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case using \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> Aeq \<Psi>eq
    by(rule_tac rPar1) (assumption | simp)+
next
  case(cPar2 Q' A\<^sub>P \<Psi>\<^sub>P)
  from \<open>A\<^sub>P \<sharp>* (A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q)\<close> have "A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>P\<^sub>Q" by simp+
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q"
                           "A\<^sub>Q \<sharp>* (P, Q, \<Psi>, M, A\<^sub>P, A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P)"
    by(rule freshFrame)
  hence "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* Q" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* M" and "A\<^sub>Q \<sharp>* A\<^sub>P" and "A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
    by simp+

  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact

  from \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> FrQ have "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain) 

  from \<open>extractFrame(P \<parallel> Q) = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>\<close> FrP FrQ \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close>
  have "\<langle>(A\<^sub>P@A\<^sub>Q), \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q\<rangle> = \<langle>A\<^sub>P\<^sub>Q, \<Psi>\<^sub>P\<^sub>Q\<rangle>" by simp
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "distinct(A\<^sub>P@A\<^sub>Q)"
    by(auto simp add: fresh_star_def fresh_def name_list_supp)
  ultimately obtain p where S: "set p \<subseteq> set(A\<^sub>P@A\<^sub>Q) \<times> set((p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q))"  and "distinctPerm p"
                        and \<Psi>eq: "\<Psi>\<^sub>P\<^sub>Q = (p \<bullet> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>Q)" and Aeq: "A\<^sub>P\<^sub>Q = (p \<bullet> A\<^sub>P)@(p \<bullet> A\<^sub>Q)"
    using \<open>A\<^sub>P \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<^sub>Q\<close> \<open>distinct A\<^sub>P\<^sub>Q\<close>
    by(rule_tac frameChainEq') (assumption | simp add: eqvts)+

  from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> Aeq
  have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" 
    by(rule_tac outputPermFrame) (assumption | simp)+
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> Aeq have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>P) \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"  
    by(simp add: eqvts)
  moreover from FrP have "(p \<bullet> extractFrame P) = p \<bullet> \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> Aeq have "extractFrame P = \<langle>(p \<bullet> A\<^sub>P), p \<bullet> \<Psi>\<^sub>P\<rangle>"
    by(simp add: eqvts)
  moreover from FrQ have "(p \<bullet> extractFrame Q) = p \<bullet> \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by simp
  with S \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> Aeq have "extractFrame Q = \<langle>(p \<bullet> A\<^sub>Q), p \<bullet> \<Psi>\<^sub>Q\<rangle>"
    by(simp add: eqvts)
  moreover from \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>Q\<close> have "distinct(p \<bullet> A\<^sub>P)" and "distinct(p \<bullet> A\<^sub>Q)"
    by simp+
  moreover from \<open>A\<^sub>Q \<sharp>* A\<^sub>P\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> A\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> \<Psi>\<^sub>Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> \<Psi>\<^sub>P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
  ultimately show ?case using \<open>A\<^sub>P\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>P\<^sub>Q \<sharp>* M\<close> Aeq \<Psi>eq
    by(rule_tac rPar2) (assumption | simp)+
qed

inductive bangPred :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
where
  aux1: "bangPred P (!P)"
| aux2: "bangPred P (P \<parallel> !P)"

lemma bangInduct[consumes 1, case_names cPar1 cPar2 cComm1 cComm2 cBang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rs   :: "('a, 'b, 'c) residual"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) residual \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto> Rs"
  and     rPar1: "\<And>\<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P' \<parallel> !P))"
  and     rPar2: "\<And>\<alpha> P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>);
                             \<And>C. Prop C \<Psi> (!P) (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P \<parallel> P'))"
  and     rComm1: "\<And>M N P' K xvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''); \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rComm2: "\<And>M xvec N P' K P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>N\<rparr> \<prec> P''); \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rBang: "\<And>Rs C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs; \<And>C. Prop C \<Psi> (P \<parallel> !P) Rs; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) Rs"
  shows "Prop C \<Psi> (!P) Rs"
proof -
  from \<open>\<Psi> \<rhd> !P \<longmapsto> Rs\<close> have "guarded P"
    by(nominal_induct \<Psi> P=="!P" Rs rule: semantics.strong_induct) (auto simp add: psi.inject)
  {
    fix Q  :: "('a, 'b, 'c) psi"
    and \<Psi>' :: 'b

    assume "\<Psi>' \<rhd> Q \<longmapsto> Rs"
    and    "guarded Q"
    and    "bangPred P Q"
    and    "\<Psi> \<simeq> \<Psi>'"

    hence "Prop C \<Psi> Q Rs" using rPar1 rPar1 rPar2 rPar2 rComm1 rComm2 rBang
    proof(nominal_induct avoiding: \<Psi> C rule: semantics.strong_induct)
      case(cInput \<Psi>' M K xvec N Tvec Q \<Psi> C)
      thus ?case by - (ind_cases "bangPred P (M\<lparr>\<lambda>*xvec N\<rparr>.Q)")
    next
      case(Output \<Psi>' M K N Q \<Psi> C)
      thus ?case by - (ind_cases "bangPred P (M\<langle>N\<rangle>.Q)")
    next
      case(Case \<Psi>' Q Rs \<phi> Cs \<Psi> C)
      thus ?case by - (ind_cases "bangPred P (Cases Cs)")
    next
      case(cPar1 \<Psi>' \<Psi>\<^sub>R Q \<alpha> P' R A\<^sub>R \<Psi> C)
      have rPar1: "\<And>\<alpha> P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P' \<parallel> !P))"
        by fact
      from \<open>bangPred P (Q \<parallel> R)\<close> have "Q = P" and "R = !P"
        by - (ind_cases "bangPred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from \<open>R = !P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> P'\<close> \<open>Q = P\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>R = \<one>\<close> have "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
        by(metis statEqTransition Identity AssertionStatEqSym)
      hence "Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P' \<parallel> !P))" using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha>  \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>Q = P\<close> \<open>distinct(bn \<alpha>)\<close>
        by(rule_tac rPar1) auto
      with \<open>R = !P\<close> \<open>Q = P\<close> show ?case by simp
    next
      case(cPar2 \<Psi>' \<Psi>\<^sub>P R \<alpha> P' Q A\<^sub>P \<Psi> C)
      have rPar2: "\<And>\<alpha> P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>);
                             \<And>C. Prop C \<Psi> (!P) (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P \<parallel> P'))"
        by fact
      from \<open>bangPred P (Q \<parallel> R)\<close> have "Q = P" and "R = !P"
        by - (ind_cases "bangPred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from \<open>Q = P\<close> \<open>extractFrame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>guarded P\<close> have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
        by(blast dest: guardedStatEq)+
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>\<alpha> \<prec> P'\<close> \<open>R = !P\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
        by(metis statEqTransition Identity Composition Commutativity AssertionStatEqSym)
      moreover
      {
        fix C
        have "bangPred P (!P)" by(rule aux1)
        moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity AssertionStatEqSym AssertionStatEqTrans)
        ultimately have "\<And>C. Prop C \<Psi> (!P) (\<alpha> \<prec> P')" using cPar2 \<open>R = !P\<close> \<open>guarded P\<close> by simp
      }
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (\<alpha> \<prec> (P \<parallel> P'))" using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha>  \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>Q = P\<close> \<open>distinct(bn \<alpha>)\<close>
        by(rule_tac rPar2) auto
      with \<open>R = !P\<close> \<open>Q = P\<close> show ?case by simp
    next
      case(cComm1 \<Psi>' \<Psi>\<^sub>R Q M N P' A\<^sub>P \<Psi>\<^sub>P R K xvec P'' A\<^sub>R \<Psi> C)
      have rComm1: "\<And>M N P' K xvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''); \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                           xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
        by fact
      from \<open>bangPred P (Q \<parallel> R)\<close> have "Q = P" and "R = !P"
        by - (ind_cases "bangPred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from \<open>R = !P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close> \<open>Q = P\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>R = \<one>\<close> have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
        by(metis statEqTransition Identity AssertionStatEqSym)
      moreover from \<open>Q = P\<close> \<open>extractFrame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>guarded P\<close> have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
        by(blast dest: guardedStatEq)+
      moreover from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''\<close> \<open>R = !P\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
        by(metis statEqTransition Identity Composition Commutativity AssertionStatEqSym)
      moreover 
      {
        fix C
        have "bangPred P (!P)" by(rule aux1)
        moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity AssertionStatEqSym AssertionStatEqTrans)
        ultimately have "\<And>C. Prop C \<Psi> (!P) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'')" using cComm1 \<open>R = !P\<close> \<open>guarded P\<close> by simp
      }
      moreover from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>R = \<one>\<close> have "\<Psi> \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Identity Composition Commutativity AssertionStatEqSym)
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* K\<close> \<open>xvec \<sharp>* C\<close> \<open>Q = P\<close> \<open>distinct xvec\<close>
        by(rule_tac rComm1) (assumption | auto)+
      with \<open>R = !P\<close> \<open>Q = P\<close> show ?case by simp
    next
      case(cComm2 \<Psi>' \<Psi>\<^sub>R Q M xvec N P' A\<^sub>P \<Psi>\<^sub>P R K P'' A\<^sub>R \<Psi> C)
      have rComm2: "\<And>M xvec N P' K P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>N\<rparr> \<prec> P''); \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                           xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
        by fact
      from \<open>bangPred P (Q \<parallel> R)\<close> have "Q = P" and "R = !P"
        by - (ind_cases "bangPred P (Q \<parallel> R)", auto simp add: psi.inject)+
      from \<open>R = !P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>R = []" and "\<Psi>\<^sub>R = \<one>" by auto
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>Q = P\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>R = \<one>\<close> have "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Identity AssertionStatEqSym)
      moreover from \<open>Q = P\<close> \<open>extractFrame Q = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>guarded P\<close> have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
        by(blast dest: guardedStatEq)+
      moreover from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> P''\<close> \<open>R = !P\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''"
        by(metis statEqTransition Identity Composition Commutativity AssertionStatEqSym)
      moreover 
      {
        fix C
        have "bangPred P (!P)" by(rule aux1)
        moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<Psi> \<simeq> \<Psi>' \<otimes> \<Psi>\<^sub>P" by(metis Composition Identity Commutativity AssertionStatEqSym AssertionStatEqTrans)
        ultimately have "\<And>C. Prop C \<Psi> (!P) (K\<lparr>N\<rparr> \<prec> P'')" using cComm2 \<open>R = !P\<close> \<open>guarded P\<close> by simp
      }
      moreover from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> \<open>\<Psi>\<^sub>R = \<one>\<close> have "\<Psi> \<turnstile> M \<leftrightarrow> K"
        by(metis statEqEnt Identity Composition Commutativity AssertionStatEqSym)
      ultimately have "Prop C \<Psi> (P \<parallel> !P) (\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close> \<open>xvec \<sharp>* K\<close> \<open>xvec \<sharp>* C\<close> \<open>Q = P\<close> \<open>distinct xvec\<close>
        by(rule_tac rComm2) (assumption | auto)+
      with \<open>R = !P\<close> \<open>Q = P\<close> show ?case by simp
    next
      case(cOpen \<Psi> Q M xvec yvec N P' x C)
      thus ?case by - (ind_cases "bangPred P (\<lparr>\<nu>x\<rparr>Q)")
    next
      case(cScope \<Psi> Q \<alpha> P' x C)
      thus ?case by - (ind_cases "bangPred P (\<lparr>\<nu>x\<rparr>Q)")
    next
      case(Bang \<Psi>' Q Rs \<Psi> C)
      have rBang: "\<And>Rs C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs; \<And>C. Prop C \<Psi> (P \<parallel> !P) Rs; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) Rs"
        by fact
      from \<open>bangPred P (!Q)\<close> have "P = Q" 
        by - (ind_cases "bangPred P (!Q)", auto simp add: psi.inject)
      with \<open>\<Psi>' \<rhd> Q \<parallel> !Q \<longmapsto> Rs\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi> \<rhd> P \<parallel> !P \<longmapsto> Rs" by(metis statEqTransition AssertionStatEqSym) 
      moreover 
      {
        fix C
        have "bangPred P (P \<parallel> !P)" by(rule aux2)
        with Bang \<open>P = Q\<close> have "\<And>C. Prop C \<Psi> (P \<parallel> !P) Rs" by simp
      }
      moreover from \<open>guarded Q\<close> \<open>P = Q\<close> have "guarded P" by simp
      ultimately have "Prop C \<Psi> (!P) Rs" by(rule rBang)
      with \<open>P = Q\<close> show ?case by simp
    qed
  }
  with \<open>guarded P\<close> \<open>\<Psi> \<rhd> !P \<longmapsto> Rs\<close>
  show ?thesis by(force intro: aux1)
qed

lemma bangInputInduct[consumes 1, case_names cPar1 cPar2 cBang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"

  assumes "\<Psi> \<rhd> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     rPar1: "\<And>P'. \<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P' \<Longrightarrow> Prop \<Psi> (P \<parallel> !P) M N (P' \<parallel> !P)"
  and     rPar2: "\<And>P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; Prop \<Psi> (!P) M N P'\<rbrakk> \<Longrightarrow> Prop \<Psi> (P \<parallel> !P) M N (P \<parallel> P')"
  and     rBang: "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; Prop \<Psi> (P \<parallel> !P) M N P'; guarded P\<rbrakk> \<Longrightarrow> Prop \<Psi> (!P) M N P'"
  shows "Prop \<Psi> (!P) M N P'"
using \<open>\<Psi> \<rhd> !P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'\<close>
by(nominal_induct \<Psi> P Rs=="M\<lparr>N\<rparr> \<prec> P'" arbitrary: P' rule: bangInduct)
  (auto simp add: residualInject intro: rPar1 rPar2 rBang)

lemma bangOutputInduct[consumes 1, case_names cPar1 cPar2 cBang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a \<Rightarrow> ('a, 'b, 'c) boundOutput \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     rPar1: "\<And>xvec N P' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P' \<parallel> !P))"
  and     rPar2: "\<And>xvec N P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<And>C. Prop C \<Psi> (!P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P'); xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> 
                                  Prop C \<Psi> (P \<parallel> !P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' (P \<parallel> P'))"
  and     rBang: "\<And>B C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>(ROut M B); \<And>C. Prop C \<Psi> (P \<parallel> !P) M B; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) M B"

  shows "Prop C \<Psi> (!P) M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')"
using \<open>\<Psi> \<rhd> !P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close>
apply(auto simp add: residualInject)
by(nominal_induct \<Psi> P Rs=="ROut M (\<lparr>\<nu>*xvec\<rparr>N \<prec>' P')" avoiding: C arbitrary: xvec N P' rule: bangInduct)
  (force simp add: residualInject intro: rPar1 rPar2 rBang)+

lemma bangTauInduct[consumes 1, case_names cPar1 cPar2 cComm1 cComm2 cBang]:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: 'd

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> P'"
  and     rPar1: "\<And>P' C. \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (P' \<parallel> !P)"
  and     rPar2: "\<And>P' C. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> P'; \<And>C. Prop C \<Psi> (!P) P'\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (P \<parallel> P')"
  and     rComm1: "\<And>M N P' K xvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rComm2: "\<And>M N P' K xvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''; \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rBang: "\<And>P' C. \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<tau> \<prec> P'; \<And>C. Prop C \<Psi> (P \<parallel> !P) P'; guarded P\<rbrakk> \<Longrightarrow> Prop C \<Psi> (!P) P'"

  shows "Prop C \<Psi> (!P) P'"
using \<open>\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> P'\<close>
by(nominal_induct \<Psi> P Rs=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: bangInduct)
  (auto simp add: residualInject intro: rPar1 rPar2 rComm1 rComm2 rBang)

lemma bangInduct'[consumes 2, case_names cAlpha cPar1 cPar2 cComm1 cComm2 cBang]:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Prop :: "'d::fs_name \<Rightarrow> 'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool"
  and   C    :: "'d::fs_name"

  assumes "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     rAlpha: "\<And>\<alpha> P' p C. \<lbrakk>bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>;  bn \<alpha> \<sharp>* C;
                                set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>)); distinctPerm p;
                                bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>; bn(p \<bullet> \<alpha>) \<sharp>* P'; Prop C \<Psi> (P \<parallel> !P) \<alpha> P'\<rbrakk> \<Longrightarrow>
                                Prop C \<Psi> (P \<parallel> !P) (p \<bullet> \<alpha>) (p \<bullet> P')"
  and     rPar1: "\<And>\<alpha> P' C.
                   \<lbrakk>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> !P) \<alpha> (P' \<parallel> !P)"
  and     rPar2: "\<And>\<alpha> P' C.
                   \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; \<And>C. Prop C \<Psi> (!P) \<alpha> P';
                    bn \<alpha> \<sharp>* \<Psi>; bn \<alpha> \<sharp>* P; bn \<alpha> \<sharp>* subject \<alpha>; bn \<alpha> \<sharp>* C; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                    Prop C \<Psi> (P \<parallel> !P) \<alpha> (P \<parallel> P')"
  and     rComm1: "\<And>M N P' K xvec P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle>) P''; \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rComm2: "\<And>M xvec N P' K P'' C. \<lbrakk>\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'; \<Psi> \<rhd> !P \<longmapsto>K\<lparr>N\<rparr> \<prec> P''; \<And>C. Prop C \<Psi> (!P) (K\<lparr>N\<rparr>) P''; \<Psi> \<turnstile> M \<leftrightarrow> K; 
                                             xvec \<sharp>* \<Psi>; xvec \<sharp>* P; xvec \<sharp>* M; xvec \<sharp>* K; xvec \<sharp>* C; distinct xvec\<rbrakk> \<Longrightarrow> Prop C \<Psi> (P \<parallel> !P) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
  and     rBang:    "\<And>\<alpha> P' C.
                     \<lbrakk>\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'; guarded P; \<And>C. Prop C \<Psi> (P \<parallel> !P) \<alpha> P'; guarded P; distinct(bn \<alpha>)\<rbrakk> \<Longrightarrow>
                      Prop C \<Psi> (!P) \<alpha> P'"
  shows "Prop C \<Psi> (!P) \<alpha> P'"
proof -
  from \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> have "distinct(bn \<alpha>)" by(rule boundOutputDistinct)
  with \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> show ?thesis
  proof(nominal_induct \<Psi> P Rs=="\<alpha> \<prec> P'" avoiding: C \<alpha> P' rule: bangInduct)
    case(cPar1 \<alpha> P' C \<alpha>' P'')
    note  \<open>\<alpha> \<prec> (P' \<parallel> !P) = \<alpha>' \<prec> P''\<close>
    moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* bn \<alpha>'" by simp
    moreover note \<open>distinct(bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
    moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P' \<parallel> !P)" by simp
    moreover from \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close> have "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp
    ultimately obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "\<alpha>' = p \<bullet> \<alpha>"
                    and  P'eq: "P'' = p \<bullet> (P' \<parallel> !P)" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> !P)"
      by(rule_tac residualEq)

    from \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> \<open>distinct(bn \<alpha>)\<close> 
    have "Prop C \<Psi> (P \<parallel> !P) \<alpha> (P' \<parallel> !P)"
      by(rule rPar1)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> S \<open>distinctPerm p\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> \<open>bn \<alpha> \<sharp>* P''\<close> \<open>\<alpha>' = (p \<bullet> \<alpha>)\<close> P'eq \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P' \<parallel> !P)\<close>
    have "Prop C \<Psi> (P \<parallel> !P) (p \<bullet> \<alpha>) (p \<bullet> (P' \<parallel> !P))"
      by(rule_tac rAlpha) 
    with P'eq \<open>\<alpha>' = p \<bullet> \<alpha>\<close> \<open>distinctPerm p\<close> show ?case  by simp
  next
    case(cPar2 \<alpha> P' C \<alpha>' P'')
    note  \<open>\<alpha> \<prec> (P \<parallel> P') = \<alpha>' \<prec> P''\<close>
    moreover from \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> have "bn \<alpha> \<sharp>* bn \<alpha>'" by simp
    moreover note \<open>distinct(bn \<alpha>)\<close> \<open>distinct(bn \<alpha>')\<close>
    moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> have "bn \<alpha> \<sharp>* (\<alpha> \<prec> P \<parallel> P')" by simp
    moreover from \<open>bn \<alpha>' \<sharp>* subject \<alpha>'\<close> have "bn \<alpha>' \<sharp>* (\<alpha>' \<prec> P'')" by simp
    ultimately obtain p where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "distinctPerm p" and "\<alpha>' = p \<bullet> \<alpha>"
                    and  P'eq: "P'' = p \<bullet> (P \<parallel> P')" and "bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>" and "bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> P')"
      by(rule_tac residualEq)
    
    note \<open>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'\<close>
    moreover from \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "\<And>C. Prop C \<Psi> (!P) \<alpha> P'" by(rule_tac cPar2) auto
    moreover note \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha>  \<sharp>* P\<close> \<open>bn \<alpha>  \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha>  \<sharp>* C\<close> \<open>distinct(bn \<alpha>)\<close>
    ultimately have "Prop C \<Psi> (P \<parallel> !P) \<alpha> (P \<parallel> P')"
      by(rule rPar2)
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>bn \<alpha> \<sharp>* C\<close> S \<open>distinctPerm p\<close> \<open>bn \<alpha> \<sharp>* \<alpha>'\<close> \<open>bn \<alpha> \<sharp>* P''\<close> \<open>\<alpha>' = (p \<bullet> \<alpha>)\<close> P'eq \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<alpha>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* (P \<parallel> P')\<close>
    have "Prop C \<Psi> (P \<parallel> !P) (p \<bullet> \<alpha>) (p \<bullet> (P \<parallel> P'))"
      by(rule_tac rAlpha) 
    with P'eq \<open>\<alpha>' = p \<bullet> \<alpha>\<close> show ?case by simp
  next
    case(cComm1 M N P' K xvec P'' C \<alpha> P''')
    hence "Prop C \<Psi> (P \<parallel> !P) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
      by(rule_tac rComm1) (assumption | simp)+
    thus ?case using \<open>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') = \<alpha> \<prec> P'''\<close>
      by(simp add: residualInject)
  next
    case(cComm2 M xvec N P' K P'' C \<alpha> P''')
    hence "Prop C \<Psi> (P \<parallel> !P) (\<tau>) (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P''))"
      by(rule_tac rComm2) (assumption | simp)+
    thus ?case using \<open>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> P'') = \<alpha> \<prec> P'''\<close>
      by(simp add: residualInject)
  next
    case(cBang C \<alpha> P')
    thus ?case by(auto intro: rBang)
  qed
qed

lemma comm1Aux:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   R'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>R   :: "name list"
  and   \<Psi>\<^sub>R   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   L    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   A\<^sub>Q   :: "name list"

  assumes RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
  and     FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
  and     PeqQ: "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct A\<^sub>R"
  and     "A\<^sub>R \<sharp>* A\<^sub>P"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* R"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* M"

  obtains K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>R \<sharp>* K'"
proof -
  from \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> FrP FrQ have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  assume Assumptions: "\<And>K'. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'; \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'; A\<^sub>R \<sharp>* K'\<rbrakk> \<Longrightarrow> thesis"
  {
    fix \<Psi>'   ::'b
    and zvec ::"name list"

    assume A: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi>'"
    assume "\<Psi>' \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
    hence "\<Psi>' \<rhd> R \<longmapsto>ROut K (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')" by(simp add: residualInject)
    moreover note FrR \<open>distinct A\<^sub>R\<close> PTrans
    moreover from \<open>\<Psi>' \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> have "distinct xvec" by(auto dest: boundOutputDistinct)
    moreover assume "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K" and "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
                and "A\<^sub>R \<sharp>* zvec" and "A\<^sub>P \<sharp>* zvec" and "zvec \<sharp>* R" and "zvec \<sharp>* P"
                and "A\<^sub>R \<sharp>* \<Psi>'"
    ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R') \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"
      using FrP \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>distinct A\<^sub>P\<close>  \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* R\<close> 
            \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close>
    proof(nominal_induct \<Psi>' R K B=="\<lparr>\<nu>*xvec\<rparr>N \<prec>' R'" A\<^sub>R \<Psi>\<^sub>R avoiding: \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec N R' arbitrary: M rule: outputFrameInduct)
      case(cAlpha \<Psi>' R K A\<^sub>R \<Psi>\<^sub>R p \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec N R' M)
      have S: "set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)" by fact
      from \<open>\<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> (\<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)"
        by(rule chanEqClosed)
      with \<open>A\<^sub>R \<sharp>* \<Psi>'\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K\<close> S \<open>distinctPerm p\<close>
      have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K" by(simp add: eqvts)
      moreover from \<open>\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> S \<open>A\<^sub>R \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>L\<rparr> \<prec> P'"
        by(rule_tac inputPermFrameSubject) auto
      with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>L\<rparr> \<prec> P'"
        by(simp add: eqvts)
      moreover from \<open>A\<^sub>P \<sharp>* M\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> M)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close> S have "A\<^sub>P \<sharp>* (p \<bullet> M)" by simp
      moreover from \<open>A\<^sub>Q \<sharp>* M\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> M)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q\<close> S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by simp
      moreover from \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<close>
      have "(p \<bullet> \<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>) \<hookrightarrow>\<^sub>F (p \<bullet> \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>)"
        by(rule FrameStatImpClosed)
      with \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>'\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close>
        \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
      have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
      ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        using cAlpha
        by metis
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')\<close> S \<open>A\<^sub>R \<sharp>* R\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close>
      have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> R \<longmapsto>(ROut (p \<bullet> K') (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R'))" using outputPermFrameSubject 
        by(auto simp add: residualInject)
      with S \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>(ROut (p \<bullet> K') (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R'))"
        by(simp add: eqvts)
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K'\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R))\<turnstile> (p \<bullet> p \<bullet> M) \<leftrightarrow> (p \<bullet> K')"
        by(rule chanEqClosed)
      with S \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> \<open>distinctPerm p\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> M \<leftrightarrow> (p \<bullet> K')"
        by(simp add: eqvts)
      moreover from \<open>zvec \<sharp>* K'\<close> have "(p \<bullet> zvec) \<sharp>* (p \<bullet> K')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* zvec\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* zvec\<close> S have "zvec \<sharp>* (p \<bullet> K')" by simp
      moreover from \<open>A\<^sub>R \<sharp>* K'\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> K')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      ultimately show ?case by blast
    next
      case(cOutput \<Psi>' M' K N R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec N' R' M)
      from \<open>A\<^sub>P \<sharp>* (M'\<langle>N\<rangle>.R)\<close> \<open>A\<^sub>Q \<sharp>* (M'\<langle>N\<rangle>.R)\<close> \<open>zvec \<sharp>* (M'\<langle>N\<rangle>.R)\<close>
      have "A\<^sub>P \<sharp>* M'" and "A\<^sub>Q \<sharp>* M'" and "zvec \<sharp>* M'" by simp+
          
      from \<open>\<Psi>' \<turnstile> M' \<leftrightarrow> K\<close> have "\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K" by(blast intro: statEqEnt Identity AssertionStatEqSym)
      hence "\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> M'" by(blast intro: chanEqSym chanEqTrans)
      with \<open>A\<^sub>Q \<sharp>* M'\<close> have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M' \<leftrightarrow> M'" by(force intro: frameImpI)
      
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close> have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M' \<leftrightarrow> M'"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* M'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M' \<leftrightarrow> M'"  by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M' \<leftrightarrow> M'" by(blast intro: statEqEnt Identity) hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> M'\<langle>N\<rangle>.R \<longmapsto>M'\<langle>N\<rangle> \<prec> R"
        by(rule Output)
      
      moreover from \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K\<close>
      have "\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'" by(metis chanEqSym chanEqTrans)
      with \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> M'"
        by(force intro: frameImpI)
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
      have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> M'"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'" 
        by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity)
      ultimately show ?case using cOutput by(auto simp add: residualInject)
    next
      case(cCase \<Psi>' R M' \<phi> Cs A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec N R' M)
      from \<open>guarded R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "\<Psi>\<^sub>R \<simeq> \<one>"
        by(metis guardedStatEq)
      with \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'\<close> have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> M'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition)
      moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      proof -
        from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>Q,  \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
        moreover from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>R  \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'" by(metis statEqTransition Identity Commutativity AssertionStatEqSym Composition)
      moreover from \<open>zvec \<sharp>* (Cases Cs)\<close> \<open>A\<^sub>P \<sharp>* (Cases Cs)\<close>  \<open>A\<^sub>Q \<sharp>* (Cases Cs)\<close> \<open>(\<phi>, R) mem Cs\<close> 
      have "A\<^sub>P \<sharp>* R" and "A\<^sub>Q \<sharp>* R" and "zvec \<sharp>* R" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>Q \<sharp>* \<phi>"
        by(auto dest: memFreshChain)
      ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R') \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"  using cCase
        by(rule_tac cCase) (assumption | simp)+
      then obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        by metis
      note RTrans \<open>(\<phi>, R) mem Cs\<close>
      moreover from \<open>\<Psi>' \<turnstile> \<phi>\<close> have "\<Psi>' \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: statEqEnt Identity AssertionStatEqSym)
      with \<open>A\<^sub>Q \<sharp>* \<phi>\<close> have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frameImpI)
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close> have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* \<phi>\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> \<phi>"  by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(blast intro: statEqEnt Identity) 
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Cases Cs \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')" using \<open>guarded R\<close> by(rule Case)
      moreover from MeqK' \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition AssertionStatEqTrans)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close>
        by fastforce
    next
      case(cPar1 \<Psi>' \<Psi>\<^sub>R\<^sub>2 R\<^sub>1 M' xvec N' R\<^sub>1' A\<^sub>R\<^sub>2 R\<^sub>2 A\<^sub>R\<^sub>1 \<Psi>\<^sub>R\<^sub>1 \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec yvec N R' M)
      have FrR2: "extractFrame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>" by fact
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'\<close> have "(\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Composition Commutativity)
      moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
      proof -
        have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>\<close>
        moreover have  "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Composition Commutativity)
      moreover from \<open>A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)\<close> \<open>extractFrame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>\<close> FrR2 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
        by(force dest: extractFrameFreshChain)+

      moreover from \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' (R\<^sub>1' \<parallel> R\<^sub>2) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'\<close> \<open>xvec \<sharp>* yvec\<close>
      obtain p T where "\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R\<^sub>1' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' T" and "R' = T \<parallel> (p \<bullet> R\<^sub>2)" and "set p \<subseteq> set yvec \<times> set xvec"
        apply(drule_tac sym)
        by(rule_tac boundOutputPar1Dest') (assumption | simp | blast dest: sym)+
      ultimately have "\<exists>K'. (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>ROut K' (\<lparr>\<nu>*yvec\<rparr>N \<prec>' T) \<and> (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> K' \<and> (A\<^sub>R\<^sub>2@zvec) \<sharp>* K' \<and> A\<^sub>R\<^sub>1 \<sharp>* K'" using cPar1
        apply(rule_tac cPar1(6)) by(assumption | simp | fastforce)+
      then  obtain K' where RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R\<^sub>1'"
                        and MeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> K'"  and "A\<^sub>R\<^sub>2 \<sharp>* K'" and "A\<^sub>R\<^sub>1 \<sharp>* K'" and "zvec \<sharp>* K'"
        using \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R\<^sub>1' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' T\<close> by(auto simp add: residualInject)
      
      from RTrans have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> R\<^sub>1 \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R\<^sub>1'"
        by(metis statEqTransition Associativity Composition Commutativity)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> (R\<^sub>1 \<parallel> R\<^sub>2) \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> (R\<^sub>1' \<parallel> R\<^sub>2)" using FrR2 \<open>xvec \<sharp>* R\<^sub>2\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* \<Psi>\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* R\<^sub>1\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* xvec\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* N'\<close>
        by(force intro: Par1)
      moreover from MeqK' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close>  \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' (R\<^sub>1' \<parallel> R\<^sub>2) = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'\<close>
        by(auto simp add: residualInject)
    next
      case(cPar2 \<Psi>' \<Psi>\<^sub>R\<^sub>1 R\<^sub>2 M' xvec N' R\<^sub>2' A\<^sub>R\<^sub>1 R\<^sub>1 A\<^sub>R\<^sub>2 \<Psi>\<^sub>R\<^sub>2 \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec yvec N R' M)
      have FrR1: "extractFrame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>" by fact
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'\<close> have "(\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Composition Commutativity)
      moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
      proof -
        have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>\<close>
        moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'"
        by(metis statEqTransition Associativity Composition Commutativity)
      moreover from \<open>A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)\<close> FrR1 \<open>extractFrame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
        by(force dest: extractFrameFreshChain)+
      moreover from \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' (R\<^sub>1 \<parallel> R\<^sub>2') = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'\<close> \<open>xvec \<sharp>* yvec\<close>
      obtain p T where "\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R\<^sub>2' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' T" and "R' = (p \<bullet> R\<^sub>1) \<parallel> T" and "set p \<subseteq> set yvec \<times> set xvec"
        apply(drule_tac sym)
        by(rule_tac boundOutputPar2Dest') (assumption | simp | blast dest: sym)+
      ultimately have "\<exists>K'. (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>ROut K' (\<lparr>\<nu>*yvec\<rparr>N \<prec>' T) \<and> (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K' \<and> (A\<^sub>R\<^sub>1@zvec) \<sharp>* K' \<and> A\<^sub>R\<^sub>2 \<sharp>* K'" using cPar2
        by(rule_tac cPar2(6)) (assumption | simp | fastforce)+
      then obtain K' where RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R\<^sub>2'"
                        and MeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"  and "A\<^sub>R\<^sub>1 \<sharp>* K'" and "zvec \<sharp>* K'" and "A\<^sub>R\<^sub>2 \<sharp>* K'" 
        using \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R\<^sub>2' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' T\<close> by(auto simp add: residualInject)
          
      from RTrans have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> R\<^sub>2 \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R\<^sub>2'"
        by(metis statEqTransition Associativity Composition Commutativity)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> (R\<^sub>1 \<parallel> R\<^sub>2) \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> (R\<^sub>1 \<parallel> R\<^sub>2')" using FrR1 \<open>xvec \<sharp>* R\<^sub>1\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* \<Psi>\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close>\<open>A\<^sub>R\<^sub>1 \<sharp>* xvec\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* N'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* R\<^sub>2\<close>
        by(force intro: Par2)
      moreover from MeqK' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close> \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' (R\<^sub>1 \<parallel> R\<^sub>2') = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'\<close>
        by(auto simp add: residualInject)
    next
      case(cOpen \<Psi>' R M' xvec yvec N' R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec zvec2 N R'' M)
      from \<open>\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>N' \<prec>' R' = \<lparr>\<nu>*zvec2\<rparr>N \<prec>' R''\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> \<open>x \<sharp> zvec2\<close> \<open>x \<sharp> R''\<close> \<open>x \<sharp> N\<close> \<open>distinct zvec2\<close>
      obtain xvec' x' yvec' where A: "\<lparr>\<nu>*(xvec@yvec)\<rparr>N' \<prec>' R' =  \<lparr>\<nu>*(xvec'@yvec')\<rparr>([(x, x')] \<bullet> N) \<prec>' ([(x, x')] \<bullet> R'')" 
                              and B: "zvec2 = (xvec'@x'#yvec')"
        by(rule_tac boundOutputOpenDest) auto
      then have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*(xvec'@yvec')\<rparr>([(x, x')] \<bullet> N) \<prec>' ([(x, x')] \<bullet> R'')) \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> (zvec) \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'" using cOpen
        by(rule_tac cOpen(4)) (assumption | simp)+
      then  obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N'\<rangle> \<prec> R'"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        using A by(auto simp add: residualInject)
      from \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>R)\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(force dest: extractFrameFreshChain)+

      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>zvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* zvec\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* zvec\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>x \<sharp> P\<close>

      obtain K'' where MeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K''" and "A\<^sub>R \<sharp>* K''" and "zvec \<sharp>* K''" and "x \<sharp> K''"
        by(rule_tac B="(x#A\<^sub>R@zvec)" in obtainPrefix) (assumption | simp | force)+
      
      from MeqK'' MeqK' have KeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity chanEqSym chanEqTrans)
      with RTrans \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* K'\<close> \<open>A\<^sub>R \<sharp>* K''\<close> \<open>A\<^sub>R \<sharp>* R\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K''\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N'\<rangle> \<prec> R'"
        by(rule_tac outputRenameSubject) (assumption | force)+
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>R \<longmapsto>K''\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N'\<rangle> \<prec> R'"
        using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> K''\<close> \<open>x \<sharp> xvec\<close> \<open> x \<sharp> yvec\<close> \<open>x \<in> supp N'\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* R\<close> \<open>x \<sharp> K''\<close>
        by(rule_tac Open) (assumption | force)+
      moreover from MeqK'' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K''\<close> \<open>x \<sharp> K''\<close> \<open>A\<^sub>R \<sharp>* K''\<close> B \<open>\<lparr>\<nu>*(xvec @ x # yvec)\<rparr>N' \<prec>' R' = \<lparr>\<nu>*zvec2\<rparr>N \<prec>' R''\<close>
        by(auto simp add: residualInject)
    next
      case(cScope \<Psi>' R M' xvec N' R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec yvec N R'' M)
      from \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' \<lparr>\<nu>x\<rparr>R' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R''\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close>
      obtain R''' where "R'' = \<lparr>\<nu>x\<rparr>R'''" and "\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'''"
        apply(drule_tac sym)
        by(rule boundOutputScopeDest) (assumption | auto)+
      then have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*yvec\<rparr>N \<prec>' R''') \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"  using cScope
        by(rule_tac cScope(4)) (assumption | simp)+
      then obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R'"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        using \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' R' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R'''\<close>
        by(auto simp add: residualInject)
      from \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>R)\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(force dest: extractFrameFreshChain)+
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>zvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* zvec\<close>  \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* zvec\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close>
      obtain K'' where MeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K''" and "x \<sharp> K''" and "A\<^sub>R \<sharp>* K''" and "zvec \<sharp>* K''"
        by(rule_tac B="(x#A\<^sub>R@zvec)" in obtainPrefix) (assumption | force)+

      from MeqK'' MeqK' have KeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity chanEqSym chanEqTrans)
      with RTrans \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* K'\<close> \<open>A\<^sub>R \<sharp>* K''\<close> \<open>A\<^sub>R \<sharp>* R\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K''\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> R'"
        by(rule_tac outputRenameSubject) (assumption | force)+
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>R \<longmapsto>K''\<lparr>\<nu>*xvec\<rparr>\<langle>N'\<rangle> \<prec> \<lparr>\<nu>x\<rparr>R'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> K''\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> N'\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* R\<close> \<open>x \<sharp> K''\<close>
        by(rule_tac Scope) (assumption | force)+
      moreover from MeqK'' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K''\<close> \<open>x \<sharp> K''\<close> \<open>A\<^sub>R \<sharp>* K''\<close> \<open>\<lparr>\<nu>*xvec\<rparr>N' \<prec>' \<lparr>\<nu>x\<rparr>R' = \<lparr>\<nu>*yvec\<rparr>N \<prec>' R''\<close>
        by(auto simp add: residualInject)
    next
      case(cBang \<Psi>' R M' A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec N R' M)
      from \<open>guarded R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "\<Psi>\<^sub>R \<simeq> \<one>"
        by(metis guardedStatEq)
      with \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'\<close> have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition)
      moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
      proof -
        from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>Q,  \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
        moreover from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'\<close> \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>L\<rparr> \<prec> P'" by(metis statEqTransition Identity Commutativity AssertionStatEqSym Composition)
      ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R') \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"  using cBang
        by(rule_tac cBang(5)) (assumption |simp)+
      then  obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        by metis
      from RTrans \<open>guarded R\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R')" by(rule Bang)
      moreover from MeqK' \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition AssertionStatEqTrans)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close>
        by force
    qed
  }
  note Goal = this
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>Q" by simp
  moreover note RTrans
  moreover from MeqK have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
    by(metis statEqEnt Associativity Commutativity)
  moreover note PeqQ \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close>
  ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>ROut K' (\<lparr>\<nu>*xvec\<rparr>N \<prec>' R') \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> ([]::name list) \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"
   by(rule_tac Goal) (assumption | force simp add: residualInject)+
  with Assumptions show ?thesis
    by(force simp add: residualInject)
qed

lemma comm2Aux:
  fixes \<Psi>    :: 'b
  and   \<Psi>\<^sub>Q   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   K    :: 'a
  and   N    :: 'a
  and   R'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>R   :: "name list"
  and   \<Psi>\<^sub>R   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   P'   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P   :: 'b
  and   A\<^sub>Q   :: "name list"

  assumes RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
  and     FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
  and     QimpP: "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "distinct A\<^sub>P"
  and     "distinct A\<^sub>R"
  and     "A\<^sub>R \<sharp>* A\<^sub>P"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* K"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* R"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* M"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* M"
  and     "A\<^sub>R \<sharp>* xvec"
  and     "xvec \<sharp>* M"

  obtains  K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>R \<sharp>* K'"
proof -
  from \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> FrP FrQ have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q"
    by(force dest: extractFrameFreshChain)+
  assume Assumptions: "\<And>K'. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'; \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'; A\<^sub>R \<sharp>* K'\<rbrakk> \<Longrightarrow> thesis"
  {
    fix \<Psi>'::'b
    fix zvec::"name list"
    assume "A\<^sub>R \<sharp>* \<Psi>'"
    assume "A\<^sub>R \<sharp>* zvec"
    assume "A\<^sub>P \<sharp>* zvec"
    assume "zvec \<sharp>* R"
    assume "zvec \<sharp>* P"
    
    assume A: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi>'"
    with RTrans have "\<Psi>' \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'" 
      by(rule statEqTransition)
    moreover note FrR \<open>distinct A\<^sub>R\<close>
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
      by(blast intro: statEqEnt Associativity AssertionStatEqSym)
    with A have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K" by(rule statEqEnt[OF Composition])
    moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" using A
      by(blast dest: frameIntComposition FrameStatEqTrans FrameStatEqSym)
    with QimpP have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(force intro: FrameStatEqImpCompose)
    moreover from PTrans have "distinct xvec" by(auto dest: boundOutputDistinct)
    ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R' \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"
      using PTrans FrP \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* \<Psi>'\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>
                       \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* zvec\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* zvec\<close> \<open>zvec \<sharp>* R\<close> \<open>zvec \<sharp>* P\<close> \<open>distinct A\<^sub>P\<close>
                       \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close>
    proof(nominal_induct avoiding: \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec arbitrary: M rule: inputFrameInduct)
      case(cAlpha \<Psi>' R K N R' A\<^sub>R \<Psi>\<^sub>R p \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      have S: "set p \<subseteq> set A\<^sub>R \<times> set (p \<bullet> A\<^sub>R)" by fact
      from \<open>\<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> M \<leftrightarrow> K\<close> have "(p \<bullet> (\<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)"
        by(rule chanEqClosed)
      with \<open>A\<^sub>R \<sharp>* \<Psi>'\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K\<close> S \<open>distinctPerm p\<close>
      have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K" by(simp add: eqvts)
      moreover from \<open>\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> S \<open>A\<^sub>R \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close> 
      have "(p \<bullet> (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"  
        using outputPermFrameSubject by(auto simp add: residualInject)
      with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(simp add: eqvts)
      moreover from \<open>A\<^sub>P \<sharp>* M\<close> have "(p \<bullet> A\<^sub>P) \<sharp>* (p \<bullet> M)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close> S have "A\<^sub>P \<sharp>* (p \<bullet> M)" by simp
      moreover from \<open>A\<^sub>Q \<sharp>* M\<close> have "(p \<bullet> A\<^sub>Q) \<sharp>* (p \<bullet> M)" 
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q\<close> S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by simp

      moreover from \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>\<close>
      have "(p \<bullet> \<langle>A\<^sub>Q, \<Psi>' \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>) \<hookrightarrow>\<^sub>F (p \<bullet> \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>)"
        by(rule FrameStatImpClosed)
      with \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>'\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>'\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close>
           \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
      have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>" by(simp add: eqvts)
      moreover from \<open>xvec \<sharp>* M\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> M)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with S \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* xvec\<close> have "xvec \<sharp>* (p \<bullet> M)" by simp
      ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        using cAlpha
        by(fastforce simp del: freshChainSimps)
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'\<close> S \<open>A\<^sub>R \<sharp>* R\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P)) \<rhd> R \<longmapsto>(p \<bullet> K')\<lparr>N\<rparr> \<prec> R'"
        by(rule_tac inputPermFrameSubject) auto
      with S \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>(p \<bullet> K')\<lparr>N\<rparr> \<prec> R'"
        by(simp add: eqvts)
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> (p \<bullet> M) \<leftrightarrow> K'\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R))\<turnstile> (p \<bullet> p \<bullet> M) \<leftrightarrow> (p \<bullet> K')"
        by(rule chanEqClosed)
      with S \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<^sub>P\<close> \<open>distinctPerm p\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> M \<leftrightarrow> (p \<bullet> K')"
        by(simp add: eqvts)
      moreover from \<open>zvec \<sharp>* K'\<close> have "(p \<bullet> zvec) \<sharp>* (p \<bullet> K')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      with \<open>A\<^sub>R \<sharp>* zvec\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* zvec\<close> S have "zvec \<sharp>* (p \<bullet> K')" by simp
      moreover from \<open>A\<^sub>R \<sharp>* K'\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> K')"
        by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
      ultimately show ?case by blast
    next
      case(cInput \<Psi>' M' K xvec N Tvec R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec yvec M)
      from \<open>A\<^sub>P \<sharp>* (M'\<lparr>\<lambda>*xvec N\<rparr>.R)\<close> \<open>A\<^sub>Q \<sharp>* (M'\<lparr>\<lambda>*xvec N\<rparr>.R)\<close> \<open>zvec \<sharp>* (M'\<lparr>\<lambda>*xvec N\<rparr>.R)\<close>
      have "A\<^sub>P \<sharp>* M'" and "A\<^sub>Q \<sharp>* M'" and "zvec \<sharp>* M'" by simp+
      
      from \<open>\<Psi>' \<turnstile> M' \<leftrightarrow> K\<close>
      have "\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K"
        by(blast intro: statEqEnt Identity AssertionStatEqSym)
      hence "\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> M'"
        by(blast intro: chanEqSym chanEqTrans)
      with \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M' \<leftrightarrow> M'"
        by(force intro: frameImpI)
      
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
      have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M' \<leftrightarrow> M'"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* M'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M' \<leftrightarrow> M'" 
        by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> M' \<leftrightarrow> M'" by(blast intro: statEqEnt Identity)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> M'\<lparr>\<lambda>*xvec N\<rparr>.R \<longmapsto>M'\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> R[xvec::=Tvec]"
        using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
        by(rule Input)
      
      moreover from \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> K\<close> \<open>\<Psi>' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K\<close>
      have "\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'" by(metis chanEqSym chanEqTrans)
      with \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* M'\<close>
      have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> M'"
        by(force intro: frameImpI)
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<close>
      have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F M \<leftrightarrow> M'"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* M'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'" 
        by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity)
      ultimately show ?case using \<open>zvec \<sharp>* M'\<close>
        by force
    next
      case(cCase \<Psi>' R M' N R' \<phi> Cs A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      from \<open>guarded R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "\<Psi>\<^sub>R \<simeq> \<one>"
        by(metis guardedStatEq)
      with \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'\<close> have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> M'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition)
      moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      proof -
        from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>Q,  \<Psi>' \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
        moreover from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>R  \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(metis statEqTransition Identity Commutativity AssertionStatEqSym Composition)
      moreover from \<open>zvec \<sharp>* (Cases Cs)\<close> \<open>A\<^sub>P \<sharp>* (Cases Cs)\<close>  \<open>A\<^sub>Q \<sharp>* (Cases Cs)\<close> \<open>(\<phi>, R) mem Cs\<close>
      have "A\<^sub>P \<sharp>* R" and "A\<^sub>Q \<sharp>* R" and "zvec \<sharp>* R" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>Q \<sharp>* \<phi>"
        by(auto dest: memFreshChain)
      ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'\<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"  using cCase
        by(rule_tac cCase) (assumption |simp)+
      then  obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        by metis
      note RTrans \<open>(\<phi>, R) mem Cs\<close>
      moreover from \<open>\<Psi>' \<turnstile> \<phi>\<close> have "\<Psi>' \<otimes> \<one> \<turnstile> \<phi>" by(blast intro: statEqEnt Identity AssertionStatEqSym)
      with \<open>A\<^sub>Q \<sharp>* \<phi>\<close> have "(\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(force intro: frameImpI)
      with \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close> have "(\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>) \<turnstile>\<^sub>F \<phi>"
        by(simp add: FrameStatImp_def)
      with \<open>A\<^sub>P \<sharp>* \<phi>\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one> \<turnstile> \<phi>"  by(force dest: frameImpE)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(blast intro: statEqEnt Identity) 
      ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Cases Cs \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'"  using \<open>guarded R\<close> by(rule Case)
      moreover from MeqK' \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition AssertionStatEqTrans)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close>
        by force
    next
      case(cPar1 \<Psi>' \<Psi>\<^sub>R\<^sub>2 R\<^sub>1 M' N R\<^sub>1' A\<^sub>R\<^sub>2 R\<^sub>2 A\<^sub>R\<^sub>1 \<Psi>\<^sub>R\<^sub>1 \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      have FrR2: "extractFrame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>" by fact
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'\<close> have "(\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Composition Commutativity)
      moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
      proof -
        have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>\<close>
        moreover have  "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Composition Commutativity)
      moreover from \<open>A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)\<close> \<open>extractFrame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>\<close> FrR2 have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
        by(force dest: extractFrameFreshChain)+
        moreover note \<open>distinct xvec\<close>

      ultimately have "\<exists>K'. (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>1' \<and> (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> K' \<and> (A\<^sub>R\<^sub>2@zvec) \<sharp>* K' \<and> A\<^sub>R\<^sub>1 \<sharp>* K'" using cPar1
        by(rule_tac cPar1(6)[where bf=xvec]) (assumption | simp | fastforce)+
      then  obtain K' where RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>1 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>1'"
                        and MeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>2) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<turnstile> M \<leftrightarrow> K'"  and "A\<^sub>R\<^sub>2 \<sharp>* K'" and "zvec \<sharp>* K'" and "A\<^sub>R\<^sub>1 \<sharp>* K'"
        by force
      
      from RTrans have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> R\<^sub>1 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>1'"
        by(metis statEqTransition Associativity Composition Commutativity)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> (R\<^sub>1 \<parallel> R\<^sub>2) \<longmapsto>K'\<lparr>N\<rparr> \<prec> (R\<^sub>1' \<parallel> R\<^sub>2)" using FrR2 \<open>A\<^sub>R\<^sub>2 \<sharp>* \<Psi>\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* R\<^sub>1\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* N\<close>
        by(force intro: Par1)
      moreover from MeqK' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close>
        by force
    next
      case(cPar2 \<Psi>' \<Psi>\<^sub>R\<^sub>1 R\<^sub>2 M' N R\<^sub>2' A\<^sub>R\<^sub>1 R\<^sub>1 A\<^sub>R\<^sub>2 \<Psi>\<^sub>R\<^sub>2 \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      have FrR1: "extractFrame R\<^sub>1 = \<langle>A\<^sub>R\<^sub>1, \<Psi>\<^sub>R\<^sub>1\<rangle>" by fact
      from \<open>\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'\<close> have "(\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> M'"
        by(metis statEqEnt Associativity Composition Commutativity)
      moreover have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
      proof -
        have "\<langle>A\<^sub>Q, (\<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>\<close>
        moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, ((\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>2\<rangle>"
          by(metis Associativity Composition Commutativity AssertionStatEqTrans AssertionStatEqSym frameNilStatEq frameResChainPres)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>R\<^sub>2 \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
        by(metis statEqTransition Associativity Composition Commutativity)
      moreover from \<open>A\<^sub>R\<^sub>1 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (R\<^sub>1 \<parallel> R\<^sub>2)\<close> FrR1 \<open>extractFrame R\<^sub>2 = \<langle>A\<^sub>R\<^sub>2, \<Psi>\<^sub>R\<^sub>2\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>1" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<^sub>2"
        by(force dest: extractFrameFreshChain)+
      ultimately have "\<exists>K'. (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>2' \<and> (\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K' \<and> (A\<^sub>R\<^sub>1@zvec) \<sharp>* K' \<and> A\<^sub>R\<^sub>2 \<sharp>* K'" using \<open>distinct xvec\<close> cPar2
        by(rule_tac cPar2(6)) (assumption | simp | fastforce)+
      then  obtain K' where RTrans: "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<rhd> R\<^sub>2 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>2'"
                        and MeqK': "(\<Psi> \<otimes> \<Psi>\<^sub>R\<^sub>1) \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"  and "A\<^sub>R\<^sub>1 \<sharp>* K'" and "zvec \<sharp>* K'" and "A\<^sub>R\<^sub>2 \<sharp>* K'"
        by force
      
      from RTrans have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<^sub>1 \<rhd> R\<^sub>2 \<longmapsto>K'\<lparr>N\<rparr> \<prec> R\<^sub>2'"
        by(metis statEqTransition Associativity Composition Commutativity)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> (R\<^sub>1 \<parallel> R\<^sub>2) \<longmapsto>K'\<lparr>N\<rparr> \<prec> (R\<^sub>1 \<parallel> R\<^sub>2')" using FrR1 \<open>A\<^sub>R\<^sub>1 \<sharp>* \<Psi>\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* R\<^sub>2\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* N\<close>
        by(force intro: Par2)
      moreover from MeqK' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<^sub>1 \<otimes> \<Psi>\<^sub>R\<^sub>2 \<turnstile> M \<leftrightarrow> K'"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>1 \<sharp>* K'\<close> \<open>A\<^sub>R\<^sub>2 \<sharp>* K'\<close>
        by force
    next
      case(cScope \<Psi>' R M' N R' x A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      then have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R' \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'" 
        by(rule_tac cScope(4)) (assumption | simp del: freshChainSimps)+
      then  obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        by metis
      from \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* (\<lparr>\<nu>x\<rparr>R)\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
        by(force dest: extractFrameFreshChain)+
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>distinct A\<^sub>P\<close> \<open>x \<sharp> P\<close> \<open>zvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>x \<sharp> A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* zvec\<close>  \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* zvec\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
      obtain K'' where MeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P \<turnstile> M \<leftrightarrow> K''" and "x \<sharp> K''" and "A\<^sub>R \<sharp>* K''" and "zvec \<sharp>* K''"
        by(rule_tac B="(x#A\<^sub>R@zvec)" in obtainPrefix) (assumption | simp | force | metis freshChainSym)+
      
      from MeqK'' MeqK' have KeqK'': "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<turnstile> K' \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity chanEqSym chanEqTrans)
      with RTrans \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* K'\<close> \<open>A\<^sub>R \<sharp>* K''\<close> \<open>A\<^sub>R \<sharp>* R\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K''\<lparr>N\<rparr> \<prec> R'"
        by(rule_tac inputRenameSubject) (assumption | force)+
      hence "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> \<lparr>\<nu>x\<rparr>R \<longmapsto>K''\<lparr>N\<rparr> \<prec> \<lparr>\<nu>x\<rparr>R'" using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>\<^sub>P\<close> \<open>x \<sharp> K''\<close> \<open>x \<sharp> N\<close>
        by(rule_tac Scope) (assumption | force)+
      moreover from MeqK'' have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K''"
        by(metis statEqEnt Associativity Composition Commutativity)
      ultimately show ?case using \<open>zvec \<sharp>* K''\<close> \<open>x \<sharp> K''\<close> \<open>A\<^sub>R \<sharp>* K''\<close>
        by force
    next
      case(cBang \<Psi>' R M' N R' A\<^sub>R \<Psi>\<^sub>R \<Psi> P A\<^sub>P \<Psi>\<^sub>P A\<^sub>Q zvec xvec M)
      from \<open>guarded R\<close> \<open>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>\<close> have "\<Psi>\<^sub>R \<simeq> \<one>"
        by(metis guardedStatEq)
      with \<open>\<Psi>' \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'\<close> have "\<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> M'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition)
      moreover have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
      proof -
        from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        moreover note \<open>\<langle>A\<^sub>Q, \<Psi>' \<otimes> \<one>\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle>\<close>
        moreover  from \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R \<otimes> \<one>\<rangle>"
          by(metis Identity Commutativity AssertionStatEqSym Composition frameResChainPres frameNilStatEq AssertionStatEqTrans)
        ultimately show ?thesis by(rule FrameStatEqImpCompose)
      qed
      moreover from \<open>\<Psi> \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'\<close> \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close>
      have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(metis statEqTransition Identity Commutativity AssertionStatEqSym Composition)
      ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'\<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K' \<and> zvec \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"  using cBang
        by(rule_tac cBang(5)) (assumption | simp del: freshChainSimps)+
      then  obtain K' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<parallel> !R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'"
                        and MeqK': "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'" and "zvec \<sharp>* K'" and "A\<^sub>R \<sharp>* K'"
        by metis
      from RTrans \<open>guarded R\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> !R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" by(rule Bang)
      moreover from MeqK' \<open>\<Psi>\<^sub>R \<simeq> \<one>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one> \<turnstile> M \<leftrightarrow> K'"
        by(metis Identity Commutativity statEqEnt AssertionStatEqSym Composition AssertionStatEqTrans)
      ultimately show ?case using \<open>zvec \<sharp>* K'\<close>
        by force
    qed
  }
  note Goal = this
  have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>Q" by(simp add: AssertionStatEqRefl)
  moreover from \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> have "A\<^sub>R \<sharp>* (\<Psi> \<otimes> \<Psi>\<^sub>Q)" by force
  ultimately have "\<exists>K'. \<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R' \<and> \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K' \<and> ([]::name list) \<sharp>* K' \<and> A\<^sub>R \<sharp>* K'"
    by(rule_tac Goal) (assumption | force)+
  with Assumptions show ?thesis
    by blast
qed

end

end
