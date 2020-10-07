(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Agent
  imports Subst_Term
begin

nominal_datatype ('term, 'assertion, 'condition) psi = 
  PsiNil ("\<zero>" 190)


| Output "'term::fs_name" 'term "('term, 'assertion::fs_name, 'condition::fs_name) psi"    ("_\<langle>_\<rangle>._" [120, 120, 110] 110)
| Input 'term "('term, 'assertion, 'condition) input"                                      ("_\<lparr>_" [120, 120] 110)
| Case "(('term, 'assertion, 'condition) psiCase)"                                         ("Case _" [120] 120)
| Par "('term, 'assertion, 'condition) psi" "('term, 'assertion, 'condition) psi"          (infixl "\<parallel>" 90)
| Res "\<guillemotleft>name\<guillemotright>(('term, 'assertion, 'condition) psi)"                                        ("\<lparr>\<nu>_\<rparr>_" [120, 120] 110)
| Assert 'assertion                                                                        ("\<lbrace>_\<rbrace>" [120] 120)
| Bang "('term, 'assertion, 'condition) psi"                                               ("!_" [110] 110)

and ('term, 'assertion, 'condition) input = 
  Trm 'term "(('term, 'assertion, 'condition) psi)"                                        ("\<rparr>_._" [130, 130] 130)
| Bind "\<guillemotleft>name\<guillemotright>(('term, 'assertion, 'condition) input)"                                     ("\<nu>__" [120, 120] 120)

and ('term, 'assertion, 'condition) psiCase = 
  EmptyCase                                                                                ("\<bottom>\<^sub>c" 120)
| Cond 'condition "(('term, 'assertion, 'condition) psi)"
                  "(('term, 'assertion, 'condition) psiCase)"                              ("\<box> _ \<Rightarrow> _ _ " [120, 120, 120] 120)

lemma psiFreshSet[simp]:
  fixes X :: "name set"
  and   M :: "'a::fs_name"
  and   N :: 'a
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   I :: "('a, 'b, 'c) input"
  and   C :: "('a, 'b, 'c) psiCase"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name
  and   \<Psi> :: 'b
  and   \<Phi> :: 'c

  shows "X \<sharp>* (M\<langle>N\<rangle>.P) = (X \<sharp>* M \<and> X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* M\<lparr>I = (X \<sharp>* M \<and> X \<sharp>* I)"
  and   "X \<sharp>* Case C = X \<sharp>* C"
  and   "X \<sharp>* (P \<parallel> Q) = (X \<sharp>* P \<and> X \<sharp>* Q)"
  and   "X \<sharp>* \<lparr>\<nu>x\<rparr>P = (X \<sharp>* [x].P)"
  and   "X \<sharp>* \<lbrace>\<Psi>\<rbrace> = X \<sharp>* \<Psi>"
  and   "X \<sharp>* !P = X \<sharp>* P"
  and   "X \<sharp>* \<zero>"
  and   "X \<sharp>* Trm N P = (X \<sharp>* N \<and> X \<sharp>* P)"
  and   "X \<sharp>* Bind x I = X \<sharp>* ([x].I)"

  and   "X \<sharp>* \<bottom>\<^sub>c"
  and   "X \<sharp>* \<box> \<Phi> \<Rightarrow> P C = (X \<sharp>* \<Phi> \<and> X \<sharp>* P \<and> X \<sharp>* C)"
by(auto simp add: fresh_star_def psi.fresh)+

lemma psiFreshVec[simp]:
  fixes xvec :: "name list"

  shows "xvec \<sharp>* (M\<langle>N\<rangle>.P) = (xvec \<sharp>* M \<and> xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* M\<lparr>I = (xvec \<sharp>* M \<and> xvec \<sharp>* I)"
  and   "xvec \<sharp>* Case C = xvec \<sharp>* C"
  and   "xvec \<sharp>* (P \<parallel> Q) = (xvec \<sharp>* P \<and> xvec \<sharp>* Q)"
  and   "xvec \<sharp>* \<lparr>\<nu>x\<rparr>P = (xvec \<sharp>* [x].P)"
  and   "xvec \<sharp>* \<lbrace>\<Psi>\<rbrace> = xvec \<sharp>* \<Psi>"
  and   "xvec \<sharp>* !P = xvec \<sharp>* P"
  and   "xvec \<sharp>* \<zero>"

  and   "xvec \<sharp>* Trm N P = (xvec \<sharp>* N \<and> xvec \<sharp>* P)"
  and   "xvec \<sharp>* Bind x I = xvec \<sharp>* ([x].I)"

  and   "xvec \<sharp>* \<bottom>\<^sub>c"
  and   "xvec \<sharp>* \<box> \<Phi> \<Rightarrow> P C = (xvec \<sharp>* \<Phi> \<and> xvec \<sharp>* P \<and> xvec \<sharp>* C)"
by(auto simp add: fresh_star_def)

fun psiCases :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list \<Rightarrow> ('a, 'b, 'c) psiCase"
where 
  base: "psiCases [] = \<bottom>\<^sub>c"
| step: "psiCases ((\<Phi>, P)#xs) = Cond \<Phi> P (psiCases xs)"

lemma psiCasesEqvt[eqvt]:
  fixes p  :: "name prm"
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"

  shows "(p \<bullet> (psiCases Cs)) = psiCases(p \<bullet> Cs)"
by(induct Cs) auto

lemma psiCasesFresh[simp]:
  fixes x  :: name
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  
  shows "x \<sharp> psiCases Cs = x \<sharp> Cs"
by(induct Cs)
  (auto simp add: fresh_list_nil fresh_list_cons)

lemma psiCasesFreshChain[simp]:
  fixes xvec :: "name list"
  and   Cs :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   Xs   :: "name set"
  
  shows "(xvec \<sharp>* psiCases Cs) = xvec \<sharp>* Cs"
  and   "(Xs \<sharp>* psiCases Cs) = Xs \<sharp>* Cs"
by(auto simp add: fresh_star_def)

abbreviation
  psiCasesJudge ("Cases _" [80] 80) where "Cases Cs \<equiv> Case(psiCases Cs)"

primrec resChain :: "name list \<Rightarrow> ('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) psi" where
  base: "resChain [] P = P"
| step: "resChain (x#xs) P = \<lparr>\<nu>x\<rparr>(resChain xs P)"

notation resChain ("\<lparr>\<nu>*_\<rparr>_" [80, 80] 80)

lemma resChainEqvt[eqvt]:
  fixes perm :: "name prm"
  and   lst  :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  
  shows "perm \<bullet> (\<lparr>\<nu>*xvec\<rparr>P) = \<lparr>\<nu>*(perm \<bullet> xvec)\<rparr>(perm \<bullet> P)"
by(induct_tac xvec, auto)

lemma resChainSupp:
  fixes xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "supp(\<lparr>\<nu>*xvec\<rparr>P) = (supp P) - set xvec"
by(induct xvec) (auto simp add: psi.supp abs_supp)

lemma resChainFresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "x \<sharp> \<lparr>\<nu>*xvec\<rparr>P = (x \<in> set xvec \<or> x \<sharp> P)"
by (induct xvec) (simp_all add: abs_fresh)

lemma resChainFreshSet: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  shows "Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> x \<sharp> P)"
  and   "yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (\<forall>x\<in>(set yvec). x \<in> set xvec \<or> x \<sharp> P)"
by (simp add: fresh_star_def resChainFresh)+

lemma resChainFreshSimps[simp]:
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"

  shows "Xs \<sharp>* xvec \<Longrightarrow> Xs \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (Xs \<sharp>* P)"
  and   "yvec \<sharp>* xvec \<Longrightarrow> yvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P) = (yvec \<sharp>* P)"
  and   "xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
apply(simp add: resChainFreshSet) apply(force simp add: fresh_star_def name_list_supp fresh_def)
apply(simp add: resChainFreshSet) apply(force simp add: fresh_star_def name_list_supp fresh_def)
by(simp add: resChainFreshSet)
  
lemma resChainAlpha:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"

  assumes xvecFreshP: "(p \<bullet> xvec) \<sharp>* P"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "\<lparr>\<nu>*xvec\<rparr>P = \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>(p \<bullet> P)"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
    by (simp add: resChainFreshSet)
  moreover from xvecFreshP have "set (p \<bullet> xvec) \<sharp>* (\<lparr>\<nu>*xvec\<rparr>P)"
    by (simp add: resChainFreshSet) (simp add: fresh_star_def)
  ultimately have "\<lparr>\<nu>*xvec\<rparr>P = p \<bullet> (\<lparr>\<nu>*xvec\<rparr>P)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma resChainAppend:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  
  shows "\<lparr>\<nu>*(xvec@yvec)\<rparr>P = \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>*yvec\<rparr>P)"
by(induct xvec) auto

lemma resChainSimps[dest]:
  fixes xvec :: "name list"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q'   :: "('a, 'b, 'c) psi"

  shows "((\<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q)) = P' \<parallel> Q') \<Longrightarrow> (P = P' \<and> Q = Q')"
  and   "(P \<parallel> Q = \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')) \<Longrightarrow> (P = P' \<and> Q = Q')"
by(case_tac xvec, simp_all add: psi.inject)+

primrec inputChain :: "name list \<Rightarrow> 'a::fs_name \<Rightarrow> ('a, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> ('a, 'b, 'c) input" where
  base: "inputChain [] N P = \<rparr>(N).P"
| step: "inputChain (x#xs) N P = \<nu> x (inputChain xs N P)"

abbreviation
  inputChainJudge ("_\<lparr>\<lambda>*_ _\<rparr>._" [80, 80, 80, 80] 80) where "M\<lparr>\<lambda>*xvec N\<rparr>.P \<equiv> M\<lparr>(inputChain xvec N P)"

lemma inputChainEqvt[eqvt]:
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  
  shows "p \<bullet> (inputChain xvec N P) = inputChain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P)"
by(induct_tac xvec) auto

lemma inputChainFresh: 
  fixes x    :: name
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "x \<sharp> (inputChain xvec N P) = (x \<in> set xvec \<or> (x \<sharp> N \<and> x \<sharp> P))"
by (induct xvec) (simp_all add: abs_fresh)

lemma inductChainSimps[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "xvec \<sharp>* (inputChain xvec N P)"
by(induct xvec) (auto simp add: abs_fresh abs_fresh_star fresh_star_def)

lemma inputChainFreshSet: 
  fixes Xs   :: "name set"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  shows "Xs \<sharp>* (inputChain xvec N P) = (\<forall>x\<in>Xs. x \<in> set xvec \<or> (x \<sharp> N \<and> x \<sharp> P))"
by (simp add: fresh_star_def inputChainFresh)

lemma inputChainAlpha:
  fixes p  :: "name prm"
  and   Xs :: "name set"
  and   Ys :: "name set"

  assumes XsFreshP: "Xs \<sharp>* (inputChain xvec N P)"
  and     YsFreshN: "Ys \<sharp>* N"
  and     YsFreshP: "Ys \<sharp>* P"
  and     S: "set p \<subseteq> Xs \<times> Ys"

  shows "(inputChain xvec N P) = (inputChain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P))"
proof -
  note pt_name_inst at_name_inst XsFreshP S
  moreover from YsFreshN YsFreshP have "Ys \<sharp>* (inputChain xvec N P)"
    by (simp add: inputChainFreshSet) (simp add: fresh_star_def)
  ultimately have "(inputChain xvec N P) = p \<bullet> (inputChain xvec N P)"
    by (rule_tac pt_freshs_freshs [symmetric])
  then show ?thesis by(simp add: eqvts)
qed

lemma inputChainAlpha':
  fixes p    :: "name prm"
  and   xvec :: "name list"
  and   N    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes xvecFreshP: "(p \<bullet> xvec) \<sharp>* P"
  and     xvecFreshN: "(p \<bullet> xvec) \<sharp>* N"
  and     S: "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"

  shows "(inputChain xvec N P) = (inputChain (p \<bullet> xvec) (p \<bullet> N) (p \<bullet> P))"
proof -
  note pt_name_inst at_name_inst S
  moreover have "set xvec \<sharp>* (inputChain xvec N P)"
    by (simp add: inputChainFreshSet)
  ultimately show ?thesis using xvecFreshN xvecFreshP 
    by(rule_tac inputChainAlpha) (simp add: fresh_star_def)+
qed

lemma alphaRes:
  fixes M :: "'a::fs_name"
  and   x :: name
  and   P :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   y :: name

  assumes yFreshP: "y \<sharp> P"

  shows "\<lparr>\<nu>x\<rparr>P = \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P)"
proof(cases "x = y")
  assume "x=y"
  thus ?thesis by simp
next
  assume "x \<noteq> y"
  with yFreshP show ?thesis
    by(perm_simp add: psi.inject alpha calc_atm fresh_left)
qed

lemma alphaInput:
  fixes x :: name
  and   I :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input"
  and   c :: name

  assumes A1: "c \<sharp> I"

  shows "\<nu> x I = \<nu> c([(x, c)] \<bullet> I)"
proof(cases "x = c")
  assume "x=c"
  thus ?thesis by simp
next
  assume "x \<noteq> c"
  with A1 show ?thesis
    by(perm_simp add: input.inject alpha calc_atm fresh_left)
qed

lemma inputChainLengthEq:
  fixes xvec :: "name list"
  and   yvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "length xvec = length yvec"
  and     "xvec \<sharp>* yvec"
  and     "distinct yvec"
  and     "yvec \<sharp>* M"
  and     "yvec \<sharp>* P"

  obtains N Q where "inputChain xvec M P = inputChain yvec N Q"
proof -
  assume "\<And>N Q. inputChain xvec M P = inputChain yvec N Q \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>N Q. inputChain xvec M P = inputChain yvec N Q"
  proof(induct n arbitrary: xvec yvec M P)
    case 0
    thus ?case by auto
  next
    case(Suc n xvec yvec M P)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    with \<open>length xvec = length yvec\<close>
    obtain y yvec' where "yvec = y#yvec'" by(case_tac yvec) auto
    from \<open>yvec = y#yvec'\<close> \<open>xvec=x#xvec'\<close> \<open>xvec \<sharp>* yvec\<close> \<open>distinct yvec\<close> \<open>length xvec = length yvec\<close> \<open>yvec \<sharp>* M\<close> \<open>yvec \<sharp>* P\<close>
    have "length xvec' = length yvec'" and "xvec' \<sharp>* yvec'" and "distinct yvec'" and "yvec' \<sharp>* M" and "yvec' \<sharp>* P"
      by simp+
    then obtain N Q where Eq: "inputChain xvec' M P = inputChain yvec' N Q" using \<open>length xvec' = n\<close>
      by(drule_tac Suc) auto
    moreover from \<open>distinct yvec\<close> \<open>yvec = y#yvec'\<close> have "y \<sharp> yvec'" by auto
    moreover from \<open>xvec \<sharp>* yvec\<close> \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> have "x \<noteq> y" and "x \<sharp> yvec'"
      by auto
    moreover from \<open>yvec \<sharp>* M\<close> \<open>yvec \<sharp>* P\<close> \<open>yvec = y#yvec'\<close> have "y \<sharp> M" and "y \<sharp> P" by auto
    hence "y \<sharp> inputChain xvec' M P" by(simp add: inputChainFresh)
    with Eq have "y \<sharp> inputChain yvec' N Q" by(simp add: inputChainFresh)
    ultimately have "\<nu> x (inputChain xvec' M P) = \<nu> y (inputChain yvec' ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q))"
      by(simp add: input.inject alpha' eqvts name_swap)
    thus ?case using \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> by force
  qed
  ultimately show ?thesis
    by blast
qed

lemma inputChainEq:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "inputChain xvec M P = inputChain yvec N Q"
  and     "xvec \<sharp>* yvec"
  and     "distinct xvec"
  and     "distinct yvec"

  obtains p where "(set p) \<subseteq> (set xvec) \<times> set (p \<bullet> xvec)" and "distinctPerm p" and "yvec = p \<bullet> xvec" and "N = p \<bullet> M" and "Q = p \<bullet> P"
proof -
  assume "\<And>p. \<lbrakk>set p \<subseteq> set xvec \<times> set (p \<bullet> xvec); distinctPerm p; yvec = p \<bullet> xvec; N = p \<bullet> M; Q = p \<bullet> P\<rbrakk> \<Longrightarrow> thesis"
  moreover obtain n where "n = length xvec" by auto
  with assms have "\<exists>p. (set p) \<subseteq> (set xvec) \<times> set (yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P"
  proof(induct n arbitrary: xvec yvec M N P Q)
    case(0 xvec yvec M N P Q)
    have Eq: "inputChain xvec M P = inputChain yvec N Q" by fact
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with Eq have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case using Eq
      by(simp add: input.inject)
  next
    case(Suc n xvec yvec M N P Q)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>inputChain xvec M P = inputChain yvec N Q\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "inputChain (x#xvec') M P = inputChain (y#yvec') N Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<nu> x (inputChain xvec' M P) = \<nu> y (inputChain yvec' N Q)"
      by simp
    from \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close> \<open>xvec \<sharp>* yvec\<close>
    have "x \<noteq> y" and "xvec' \<sharp>* yvec'" and "x \<sharp> yvec'" and "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    from \<open>distinct xvec\<close> \<open>distinct yvec\<close> \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close> have "x \<sharp> xvec'" and "y \<sharp> yvec'" and "distinct xvec'" and "distinct yvec'"
      by simp+
    have IH: "\<And>xvec yvec M N P Q. \<lbrakk>inputChain xvec (M::'a) (P::('a, 'b, 'c) psi) = inputChain yvec (N::'a) (Q::('a, 'b, 'c) psi); xvec \<sharp>* yvec; distinct xvec; distinct yvec; n = length xvec\<rbrakk> \<Longrightarrow> \<exists>p. (set p) \<subseteq> (set xvec) \<times> (set yvec) \<and> distinctPerm p \<and>  yvec = p \<bullet> xvec \<and> N = p \<bullet> M \<and> Q = p \<bullet> P"
      by fact
    from EQ \<open>x \<noteq> y\<close>  \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> yvec'\<close> have "inputChain xvec' M P = inputChain yvec' ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
      by(simp add: input.inject alpha eqvts)
    with \<open>xvec' \<sharp>* yvec'\<close> \<open>distinct xvec'\<close> \<open>distinct yvec'\<close> \<open>length xvec' = n\<close> IH
    obtain p where S: "(set p) \<subseteq> (set xvec') \<times> (set yvec')" and "distinctPerm p" and "yvec' = p \<bullet> xvec'" and "([(x, y)] \<bullet> N) = p \<bullet> M" and "([(x, y)] \<bullet> Q) = p \<bullet> P"
      by metis
    from S have "set((x, y)#p) \<subseteq> set(x#xvec') \<times> set(y#yvec')" by auto
    moreover from \<open>x \<sharp> xvec'\<close> \<open>x \<sharp> yvec'\<close> \<open>y \<sharp> xvec'\<close> \<open>y \<sharp> yvec'\<close> S have "x \<sharp> p" and "y \<sharp> p"
      apply(induct p)
      by(auto simp add: fresh_list_nil fresh_list_cons fresh_prod name_list_supp) (auto simp add: fresh_def) 

    with S \<open>distinctPerm p\<close> \<open>x \<noteq> y\<close> have "distinctPerm((x, y)#p)" by auto
    moreover from \<open>yvec' = p \<bullet> xvec'\<close> \<open>x \<sharp> p\<close> \<open>y \<sharp> p\<close> \<open>x \<sharp> xvec'\<close> \<open>y \<sharp> xvec'\<close> have "(y#yvec') = ((x, y)#p) \<bullet> (x#xvec')"
      by(simp add: calc_atm freshChainSimps)
    moreover from \<open>([(x, y)] \<bullet> N) = p \<bullet> M\<close> have "([(x, y)] \<bullet> [(x, y)] \<bullet> N) = [(x, y)] \<bullet> p \<bullet> M"
      by(simp add: pt_bij)
    hence "N = ((x, y)#p) \<bullet> M" by simp
    moreover from \<open>([(x, y)] \<bullet> Q) = p \<bullet> P\<close> have "([(x, y)] \<bullet> [(x, y)] \<bullet> Q) = [(x, y)] \<bullet> p \<bullet> P"
      by(simp add: pt_bij)
    hence "Q = ((x, y)#p) \<bullet> P" by simp
    ultimately show ?case using \<open>xvec=x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      by blast
  qed
  ultimately show ?thesis by blast
qed

lemma inputChainEqLength:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes "inputChain xvec M P = inputChain yvec N Q"

  shows "length xvec = length yvec"
proof -
  obtain n where "n = length xvec" by auto
  with assms show ?thesis
  proof(induct n arbitrary: xvec yvec M P N Q)
    case(0 xvec yvec M P N Q)
    from \<open>0 = length xvec\<close> have "xvec = []" by auto
    moreover with \<open>inputChain xvec M P = inputChain yvec N Q\<close> have "yvec = []"
      by(case_tac yvec) auto
    ultimately show ?case by simp
  next
    case(Suc n xvec yvec M P N Q)
    from \<open>Suc n = length xvec\<close>
    obtain x xvec' where "xvec = x#xvec'" and "length xvec' = n"
      by(case_tac xvec) auto
    from \<open>inputChain xvec M P = inputChain yvec N Q\<close> \<open>xvec = x # xvec'\<close>
    obtain y yvec' where "inputChain (x#xvec') M P = inputChain (y#yvec') N Q"
      and "yvec = y#yvec'"
      by(case_tac yvec) auto
    hence EQ: "\<nu> x (inputChain xvec' M P) = \<nu> y (inputChain yvec' N Q)"
      by simp
    have IH: "\<And>xvec yvec M P N Q. \<lbrakk>inputChain xvec (M::'a) (P::('a, 'b, 'c) psi) = inputChain yvec N Q; n = length xvec\<rbrakk> \<Longrightarrow> length xvec = length yvec"
      by fact
    show ?case
    proof(case_tac "x = y")
      assume "x = y"
      with EQ have "inputChain xvec' M P = inputChain yvec' N Q"
        by(simp add: alpha input.inject)
      with IH \<open>length xvec' = n\<close> have "length xvec' = length yvec'"
        by blast
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      show ?case by simp
    next
      assume "x \<noteq> y"
      with EQ have "inputChain xvec' M P = inputChain ([(x, y)] \<bullet> yvec') ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
        by(simp add: alpha input.inject eqvts)
      with IH \<open>length xvec' = n\<close> have "length xvec' = length ([(x, y)] \<bullet> yvec')"
        by blast
      hence "length xvec' = length yvec'"
        by simp
      with \<open>xvec = x#xvec'\<close> \<open>yvec=y#yvec'\<close>
      show ?case by simp
    qed
  qed
qed

lemma alphaInputChain:
  fixes yvec :: "name list"
  and   xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"

  assumes "length xvec = length yvec"
  and     "yvec \<sharp>* M"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* xvec"
  and     "distinct yvec"

  shows "inputChain xvec M P = inputChain yvec ([xvec yvec] \<bullet>\<^sub>v M) ([xvec yvec] \<bullet>\<^sub>v P)"
using assms
proof(induct rule: composePermInduct)
  case cBase
  show ?case by simp
next
  case(cStep x xvec y yvec)
  thus ?case 
    apply auto
    by(subst alphaInput[of y]) (auto simp add: inputChainFresh eqvts)
qed

lemma inputChainInject[simp]:

  shows "(inputChain xvec M P = inputChain xvec N Q) = ((M = N) \<and> (P = Q))"
by(induct xvec) (auto simp add: input.inject alpha)

lemma alphaInputDistinct:
  fixes xvec :: "name list"
  and   M    :: "'a::fs_name"
  and   P    :: "('a, 'b::fs_name, 'c::fs_name) psi"
  and   yvec :: "name list"
  and   N    :: 'a
  and   Q    :: "('a, 'b, 'c) psi"

  assumes Eq: "inputChain xvec M P = inputChain yvec N Q"
  and     xvecDist: "distinct xvec"
  and     Mem: "\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp M"
  and     xvecFreshyvec: "xvec \<sharp>* yvec"
  and     xvecFreshN: "xvec \<sharp>* N"
  and     xvecFreshQ: "xvec \<sharp>* Q"

  shows "distinct yvec"
proof -
  from Eq have "length xvec = length yvec"
    by(rule inputChainEqLength)
  with assms show ?thesis
  proof(induct n=="length xvec" arbitrary: xvec yvec N Q rule: nat.induct)
    case(zero xvec yvec N Q)
    thus ?case by simp
  next
    case(Suc n xvec yvec N Q)
    have L: "length xvec = length yvec" and "Suc n = length xvec" by fact+
    then obtain x xvec' y yvec' where xEq: "xvec = x#xvec'" and yEq: "yvec = y#yvec'"
                                  and L': "length xvec' = length yvec'"
      by(cases xvec, auto, cases yvec, auto)
    have xvecFreshyvec: "xvec \<sharp>* yvec" and xvecDist: "distinct xvec" by fact+
    with xEq yEq have xineqy: "x \<noteq> y" and xvec'Freshyvec': "xvec' \<sharp>* yvec'"
                  and xvec'Dist: "distinct xvec'" and xFreshxvec': "x \<sharp> xvec'"
                  and xFreshyvec': "x \<sharp> yvec'" and yFreshxvec': "y \<sharp> xvec'"
      by(auto simp add: fresh_list_cons)
    have Eq: "inputChain xvec M P = inputChain yvec N Q" by fact
    with xEq yEq xineqy have Eq': "inputChain xvec' M P = inputChain ([(x, y)] \<bullet> yvec') ([(x, y)] \<bullet> N) ([(x, y)] \<bullet> Q)"
      by(simp add: input.inject alpha eqvts) 
    moreover have Mem:"\<And>x. x \<in> set xvec \<Longrightarrow> x \<in> supp M" by fact
    with xEq have "\<And>x. x \<in> set xvec' \<Longrightarrow> x \<in> supp M" by simp
    moreover have xvecFreshN: "xvec \<sharp>* N" by fact
    with xEq xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> N)" by simp
    moreover have xvecFreshQ: "xvec \<sharp>* Q" by fact
    with xEq xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> Q)" by simp
    moreover have "Suc n = length xvec" by fact
    with xEq have "n = length xvec'" by simp
    moreover from xvec'Freshyvec' xFreshxvec' yFreshxvec' have "xvec' \<sharp>* ([(x, y)] \<bullet> yvec')"
      by simp
    moreover from L' have "length xvec' = length([(x, y)] \<bullet> yvec')" by simp
    ultimately have "distinct([(x, y)] \<bullet> yvec')" using xvec'Dist
      by(rule_tac Suc)
    hence "distinct yvec'" by simp
    from Mem xEq have xSuppM: "x \<in> supp M" by simp
    from L xvecFreshyvec xvecDist xvecFreshN xvecFreshQ
    have "inputChain yvec N Q = inputChain xvec ([yvec xvec] \<bullet>\<^sub>v N) ([yvec xvec] \<bullet>\<^sub>v Q)"
      by(simp add: alphaInputChain)
    with Eq have "M = [yvec xvec] \<bullet>\<^sub>v N"  by auto
    with xEq yEq have "M = [(y, x)] \<bullet> [yvec' xvec'] \<bullet>\<^sub>v N"
      by simp
    with xSuppM have ySuppN: "y \<in> supp([yvec' xvec'] \<bullet>\<^sub>v N)"
      by(drule_tac pi="[(x, y)]" in pt_set_bij2[OF pt_name_inst, OF at_name_inst])
        (simp add: calc_atm eqvts name_swap)
    have "y \<sharp> yvec'"
    proof(simp add: fresh_def, rule notI)
      assume "y \<in> supp yvec'"
      hence "y mem yvec'"
        by(induct yvec') (auto simp add: supp_list_nil supp_list_cons supp_atm)
      moreover from xvecFreshN xEq xFreshxvec' have "xvec' \<sharp>* N" by simp
      ultimately have "y \<sharp> [yvec' xvec'] \<bullet>\<^sub>v  N" using L' xvec'Freshyvec' xvec'Dist
        by(force intro: freshChainPerm simp add: freshChainSym)
      with ySuppN show "False" by(simp add: fresh_def)
    qed
    with \<open>distinct yvec'\<close>  yEq show ?case by simp
  qed
qed

lemma psiCasesInject[simp]:
  fixes CsP  :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"

  shows "(psiCases CsP = psiCases CsQ) = (CsP = CsQ)"
proof(induct CsP arbitrary: CsQ)
  case(Nil CsQ)
  thus ?case by(case_tac CsQ) (auto)
next
  case(Cons a CsP CsQ)
  thus ?case
    by(case_tac a, case_tac CsQ) (clarsimp simp add: psiCase.inject)+
qed

lemma casesInject[simp]:
  fixes CsP :: "('c::fs_name \<times> ('a::fs_name, 'b::fs_name, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

  shows "(Cases CsP = Cases CsQ) = (CsP = CsQ)"
apply(induct CsP)
apply(auto simp add: psiCase.inject)
apply(case_tac CsQ)
apply(simp add: psiCase.inject psi.inject)
apply(force simp add: psiCase.inject psi.inject)
apply(case_tac CsQ)
apply(force simp add: psiCase.inject psi.inject)
apply(auto simp add: psiCase.inject psi.inject)
apply(simp only: psiCases.simps[symmetric])
apply(simp only: psiCasesInject)
apply simp
apply(case_tac CsQ)
by(auto simp add: psiCase.inject psi.inject)

nominal_primrec
  guarded :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> bool"
  and guarded'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> bool"
  and guarded'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase \<Rightarrow> bool"

where
  "guarded (\<zero>) = True"
| "guarded (M\<langle>N\<rangle>.P) = True"
| "guarded (M\<lparr>I) = True"
| "guarded (Case C) = guarded'' C"
| "guarded (P \<parallel> Q) = ((guarded P) \<and> (guarded Q))"
| "guarded (\<lparr>\<nu>x\<rparr>P) = (guarded P)"
| "guarded (\<lbrace>\<Psi>\<rbrace>) = False"
| "guarded (!P) = guarded P"

| "guarded' (Trm M P) = False"
| "guarded' (\<nu> y I) = False"

| "guarded'' (\<bottom>\<^sub>c) = True"
| "guarded'' (\<box>\<phi> \<Rightarrow> P C) = (guarded P \<and> guarded'' C)"
apply(finite_guess)+
apply(rule TrueI)+
by(fresh_guess add: fresh_bool)+

lemma guardedEqvt[eqvt]:
  fixes p    :: "name prm"
  and   P    :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  shows "(p \<bullet> (guarded P)) = guarded (p \<bullet> P)"
  and   "(p \<bullet> (guarded' I)) = guarded' (p \<bullet> I)"
  and   "(p \<bullet> (guarded'' C)) = guarded'' (p \<bullet> C)"
by(nominal_induct P and I and C rule: psi_input_psiCase.strong_inducts)
  (simp add: eqvts)+

lemma guardedClosed[simp]:
  fixes P :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi"
  and   p :: "name prm"

  assumes "guarded P"

  shows "guarded(p \<bullet> P)"
proof -
  from \<open>guarded P\<close> have "p \<bullet> (guarded P)"
    by(simp add: perm_bool)
  thus ?thesis by(simp add: eqvts)
qed

locale substPsi =
  substTerm?: substType substTerm +
  substAssert?: substType substAssert +
  substCond?: substType substCond

  for substTerm :: "('a::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'a"
  and substAssert :: "('b::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'b"
  and substCond :: "('c::fs_name) \<Rightarrow> name list \<Rightarrow> 'a::fs_name list \<Rightarrow> 'c"
begin

nominal_primrec 
    subs   :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psi \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b, 'c) psi"
and subs'  :: "('a::fs_name, 'b::fs_name, 'c::fs_name) input \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b, 'c) input"
and subs'' :: "('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase \<Rightarrow> name list \<Rightarrow> 'a list  \<Rightarrow> ('a, 'b, 'c) psiCase"

where
  "subs (\<zero>) xvec Tvec = \<zero>"
| "(subs (M\<langle>N\<rangle>.P) xvec Tvec) = (substTerm M xvec Tvec)\<langle>(substTerm N xvec Tvec)\<rangle>.(subs P xvec Tvec)"
| "(subs (M\<lparr>I) xvec Tvec) = (substTerm M xvec Tvec)\<lparr>(subs' I xvec Tvec)"

| "(subs (Case C) xvec Tvec) = (Case (subs'' C xvec Tvec))"
| "(subs (P \<parallel> Q) xvec Tvec) = (subs P xvec Tvec) \<parallel> (subs Q xvec Tvec)"
| "\<lbrakk>y \<sharp> xvec; y \<sharp> Tvec\<rbrakk> \<Longrightarrow> (subs (\<lparr>\<nu>y\<rparr>P) xvec Tvec) = \<lparr>\<nu>y\<rparr>(subs P xvec Tvec)"
| "(subs (\<lbrace>\<Psi>\<rbrace>) xvec Tvec) = \<lbrace>(substAssert \<Psi> xvec Tvec)\<rbrace>"
| "(subs (!P) xvec Tvec) = !(subs P xvec Tvec)"

| "(subs' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) xvec Tvec) = (\<rparr>(substTerm M xvec Tvec).(subs P xvec Tvec))"
| "\<lbrakk>y \<sharp> xvec; y \<sharp> Tvec\<rbrakk> \<Longrightarrow> (subs' (\<nu> y I) xvec Tvec) = (\<nu> y (subs' I xvec Tvec))"

| "(subs'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase) xvec Tvec) = \<bottom>\<^sub>c"
| "(subs'' (\<box>\<Phi> \<Rightarrow> P C) xvec Tvec) = (\<box>(substCond \<Phi> xvec Tvec) \<Rightarrow> (subs P xvec Tvec) (subs'' C xvec Tvec))"
apply(finite_guess add: substTerm.fs substAssert.fs substCond.fs)+
apply(rule TrueI)+
apply(simp add: abs_fresh)
apply(simp add: abs_fresh)
apply(simp add: abs_fresh)
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
apply(fresh_guess)+
apply(rule supports_fresh[of "supp(xvec, Tvec)"])
apply(force simp add: perm_fun_def eqvts fresh_def[symmetric] supports_def)
apply(simp add: fs_name1)
apply(simp add: fresh_def[symmetric])
done

lemma substEqvt[eqvt]:
  fixes p    :: "name prm"
  and   P    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"
  and   Tvec :: "'a list"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  shows "(p \<bullet> (subs P xvec Tvec)) = subs (p \<bullet> P) (p \<bullet> xvec) (p \<bullet> Tvec)"
  and   "(p \<bullet> (subs' I xvec Tvec)) = subs' (p \<bullet> I) (p \<bullet> xvec) (p \<bullet> Tvec)"
  and   "(p \<bullet> (subs'' C xvec Tvec)) = subs'' (p \<bullet> C) (p \<bullet> xvec) (p \<bullet> Tvec)"
apply(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psiCase.strong_inducts)
apply(auto simp add: eqvts)
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply simp
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
apply(drule_tac pi=p in pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
by simp

lemma subst2[intro]:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   x    :: name
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  assumes "x \<sharp> Tvec"
  and     "x \<sharp> xvec"

  shows "x \<sharp> P \<Longrightarrow> x \<sharp> (subs P xvec Tvec)"
  and   "x \<sharp> I \<Longrightarrow> x \<sharp> (subs' I xvec Tvec)"
  and   "x \<sharp> C \<Longrightarrow> x \<sharp> (subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psiCase.strong_inducts)
  (auto intro: substTerm.subst2 substCond.subst2 substAssert.subst2 simp add: abs_fresh)

lemma subst2Chain[intro]:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   Xs   :: "name set"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  assumes "Xs \<sharp>* xvec"
  and     "Xs \<sharp>* Tvec"

  shows "Xs \<sharp>* P \<Longrightarrow> Xs \<sharp>* (subs P xvec Tvec)"
  and   "Xs \<sharp>* I \<Longrightarrow> Xs \<sharp>* (subs' I xvec Tvec)"
  and   "Xs \<sharp>* C \<Longrightarrow> Xs \<sharp>* (subs'' C xvec Tvec)"
using assms
by(auto intro: subst2 simp add: fresh_star_def)

lemma renaming:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   p    :: "name prm"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a ,'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  assumes "length xvec = length Tvec"
  and     "set p \<subseteq> set xvec \<times> set (p \<bullet> xvec)"
  and     "distinctPerm p"

  shows "\<lbrakk>(p \<bullet> xvec) \<sharp>* P\<rbrakk> \<Longrightarrow> (subs P xvec Tvec) = subs (p \<bullet> P) (p \<bullet> xvec) Tvec"
  and   "\<lbrakk>(p \<bullet> xvec) \<sharp>* I\<rbrakk> \<Longrightarrow> (subs' I xvec Tvec) = subs' (p \<bullet> I) (p \<bullet> xvec) Tvec"
  and   "\<lbrakk>(p \<bullet> xvec) \<sharp>* C\<rbrakk> \<Longrightarrow> (subs'' C xvec Tvec) = subs'' (p \<bullet> C) (p \<bullet> xvec) Tvec"
using assms
by(nominal_induct P and I and C avoiding: xvec p Tvec rule: psi_input_psiCase.strong_inducts)
  (auto intro: substTerm.renaming substCond.renaming substAssert.renaming simp add: freshChainSimps psi.inject input.inject psiCase.inject)

lemma subst4Chain:
  fixes xvec :: "name list"
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"
  and     "xvec \<sharp>* Tvec"

  shows "xvec \<sharp>* (subs P xvec Tvec)"
  and   "xvec \<sharp>* (subs' I xvec Tvec)"
  and   "xvec \<sharp>* (subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psiCase.strong_inducts)
  (auto intro: substTerm.subst4Chain substCond.subst4Chain substAssert.subst4Chain simp add: abs_fresh)

lemma guardedSubst[simp]:
  fixes P    :: "('a, 'b, 'c) psi"
  and   I    :: "('a, 'b, 'c) input"
  and   C    :: "('a, 'b, 'c) psiCase"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  assumes "length xvec = length Tvec"
  and     "distinct xvec"

  shows "guarded P \<Longrightarrow> guarded(subs P xvec Tvec)"
  and   "guarded' I \<Longrightarrow> guarded'(subs' I xvec Tvec)"
  and   "guarded'' C \<Longrightarrow> guarded''(subs'' C xvec Tvec)"
using assms
by(nominal_induct P and I and C avoiding: xvec Tvec rule: psi_input_psiCase.strong_inducts) auto

definition seqSubs :: "('a, 'b, 'c) psi \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) psi" ("_[<_>]" [80, 80] 130)
  where "P[<\<sigma>>] \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs Q xvec Tvec) P \<sigma>"

definition seqSubs' :: "('a, 'b, 'c) input \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) input" 
  where "seqSubs' I \<sigma> \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs' Q xvec Tvec) I \<sigma>"

definition seqSubs'' :: "('a, 'b, 'c) psiCase \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('a, 'b, 'c) psiCase"
  where "seqSubs'' C \<sigma> \<equiv> foldl (\<lambda>Q. \<lambda>(xvec, Tvec). subs'' Q xvec Tvec) C \<sigma>"

lemma substInputChain[simp]:
  fixes xvec :: "name list"
  and   N    :: "'a"
  and   P    :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"
  and   Tvec :: "'a list"

  assumes "xvec \<sharp>* yvec"
  and     "xvec \<sharp>* Tvec"

  shows "subs' (inputChain xvec N P) yvec Tvec = inputChain xvec (substTerm N yvec Tvec) (subs P yvec Tvec)"
using assms
by(induct xvec) (auto simp add: psi.inject)

fun caseListSubst :: "('c \<times> ('a, 'b, 'c) psi) list \<Rightarrow> name list \<Rightarrow> 'a list \<Rightarrow> ('c \<times> ('a, 'b, 'c) psi) list"
where
  "caseListSubst [] _ _ = []"
| "caseListSubst ((\<phi>, P)#Cs) xvec Tvec = (substCond \<phi> xvec Tvec, (subs P xvec Tvec))#(caseListSubst Cs xvec Tvec)"

lemma substCases[simp]:
  fixes Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  shows "subs (Cases Cs) xvec Tvec = Cases(caseListSubst Cs xvec Tvec)"
by(induct Cs) (auto simp add: psi.inject)

lemma substCases'[simp]:
  fixes Cs   :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   xvec :: "name list"
  and   Tvec :: "'a list"

  shows "(subs'' (psiCases Cs) xvec Tvec) = psiCases(caseListSubst Cs xvec Tvec)"
by(induct Cs) auto

lemma seqSubstSimps[simp]:
  shows "seqSubs (\<zero>) \<sigma> = \<zero>"
  and   "(seqSubs (M\<langle>N\<rangle>.P) \<sigma>) = (substTerm.seqSubst M \<sigma>)\<langle>(substTerm.seqSubst N \<sigma>)\<rangle>.(seqSubs P \<sigma>)"
  and   "(seqSubs (M\<lparr>I) \<sigma>) = (substTerm.seqSubst M \<sigma>)\<lparr>(seqSubs' I \<sigma>)"

  and   "(seqSubs (Case C) \<sigma>) = (Case (seqSubs'' C \<sigma>))"
  and   "(seqSubs (P \<parallel> Q) \<sigma>) = (seqSubs P \<sigma>) \<parallel> (seqSubs Q \<sigma>)"
  and   "\<lbrakk>y \<sharp> \<sigma>\<rbrakk> \<Longrightarrow> (seqSubs (\<lparr>\<nu>y\<rparr>P) \<sigma>) = \<lparr>\<nu>y\<rparr>(seqSubs P \<sigma>)"
  and   "(seqSubs (\<lbrace>\<Psi>\<rbrace>) \<sigma>) = \<lbrace>(substAssert.seqSubst \<Psi> \<sigma>)\<rbrace>"
  and   "(seqSubs (!P) \<sigma>) = !(seqSubs P \<sigma>)"
  
  and   "(seqSubs' ((Trm M P)::('a::fs_name, 'b::fs_name, 'c::fs_name) input) \<sigma>) = (\<rparr>(substTerm.seqSubst M \<sigma>).(seqSubs P \<sigma>))"
  and   "\<lbrakk>y \<sharp> \<sigma>\<rbrakk> \<Longrightarrow> (seqSubs' (\<nu> y I) \<sigma>) = (\<nu> y (seqSubs' I \<sigma>))"
  
  and   "(seqSubs'' (\<bottom>\<^sub>c::('a::fs_name, 'b::fs_name, 'c::fs_name) psiCase) \<sigma>) = \<bottom>\<^sub>c"
  and   "(seqSubs'' (\<box>\<Phi> \<Rightarrow> P C) \<sigma>) = (\<box>(substCond.seqSubst \<Phi> \<sigma>) \<Rightarrow> (seqSubs P \<sigma>) (seqSubs'' C \<sigma>))"
by(induct \<sigma> arbitrary: M N P I C Q \<Psi> \<Phi>, auto simp add: seqSubs_def seqSubs'_def seqSubs''_def)

lemma seqSubsNil[simp]:
  "seqSubs P [] = P"
by(simp add: seqSubs_def)

lemma seqSubsCons[simp]:
  shows "seqSubs P ((xvec, Tvec)#\<sigma>) = seqSubs(subs P xvec Tvec) \<sigma>"
  by(simp add: seqSubs_def)

lemma seqSubsTermAppend[simp]:
  shows "seqSubs P (\<sigma>@\<sigma>') = seqSubs (seqSubs P \<sigma>) \<sigma>'"
by(induct \<sigma>) (auto simp add: seqSubs_def)

fun caseListSeqSubst :: "('c \<times> ('a, 'b, 'c) psi) list \<Rightarrow> (name list \<times> 'a list) list \<Rightarrow> ('c \<times> ('a, 'b, 'c) psi) list"
where
  "caseListSeqSubst [] _ = []"
| "caseListSeqSubst ((\<phi>, P)#Cs) \<sigma> = (substCond.seqSubst \<phi> \<sigma>, (seqSubs P \<sigma>))#(caseListSeqSubst Cs \<sigma>)"

lemma seqSubstCases[simp]:
  fixes Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<sigma>  :: "(name list \<times> 'a list) list"

  shows "seqSubs (Cases Cs) \<sigma> = Cases(caseListSeqSubst Cs \<sigma>)"
by(induct Cs) (auto simp add: psi.inject)

lemma seqSubstCases'[simp]:
  fixes Cs :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   \<sigma>  :: "(name list \<times> 'a list) list"

  shows "(seqSubs'' (psiCases Cs) \<sigma>) = psiCases(caseListSeqSubst Cs \<sigma>)"
by(induct Cs) auto

lemma seqSubstEqvt[eqvt]:
  fixes P :: "('a, 'b, 'c) psi"
  and   \<sigma> :: "(name list \<times> 'a list) list"
  and   p :: "name prm"

  shows "(p \<bullet> (P[<\<sigma>>])) = (p \<bullet> P)[<(p \<bullet> \<sigma>)>]"
by(induct \<sigma> arbitrary: P) (auto simp add: eqvts seqSubs_def)

lemma guardedSeqSubst:
  assumes "guarded P"
  and     "wellFormedSubst \<sigma>"

  shows "guarded(seqSubs P \<sigma>)"
using assms
by(induct \<sigma> arbitrary: P) (auto dest: guardedSubst)

end

lemma inter_eqvt:
  shows "(pi::name prm) \<bullet> ((X::name set) \<inter> Y) = (pi \<bullet> X) \<inter> (pi \<bullet> Y)"
by(auto simp add: perm_set_def perm_bij)

lemma delete_eqvt:
  fixes p :: "name prm"
  and   X :: "name set"
  and   Y :: "name set"

  shows "p \<bullet> (X - Y) = (p \<bullet> X) - (p \<bullet> Y)"
by(auto simp add: perm_set_def perm_bij)

lemma perm_singleton[simp]:
  shows "(p::name prm) \<bullet> {(x::name)} = {p \<bullet> x}"
by(auto simp add: perm_set_def)

end
