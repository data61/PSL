(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Sim
  imports Tau Sum
begin

nominal_datatype 'a prefix =
  pInput "'a::fs_name" "name list" 'a
| pOutput 'a 'a                           
| pTau                                    

context tau
begin

nominal_primrec bindPrefix :: "'a prefix \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi"  ("_\<cdot>_" [100, 100] 100)
where
  "bindPrefix (pInput M xvec N) P = M\<lparr>\<lambda>*xvec N\<rparr>.P"
| "bindPrefix (pOutput M N) P = M\<langle>N\<rangle>.P"
| "bindPrefix (pTau) P = \<tau>.(P)"
by(rule TrueI)+

lemma bindPrefixEqvt[eqvt]:
  fixes p :: "name prm"
  and   \<alpha> :: "'a prefix"
  and   P :: "('a, 'b, 'c) psi"

  shows "(p \<bullet> (\<alpha>\<cdot>P)) = (p \<bullet> \<alpha>)\<cdot>(p \<bullet> P)"
by(nominal_induct \<alpha> rule: prefix.strong_inducts) (auto simp add: eqvts)

lemma prefixCases[consumes 1, case_names cInput cOutput cTau]:
  fixes \<Psi> :: 'b
  and   \<alpha>  :: "'a prefix"
  and   P  :: "('a, 'b, 'c) psi"
  and   \<beta>  :: "'a action"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<beta> \<prec> P'"
  and     rInput: "\<And>M xvec N K Tvec. \<lbrakk>\<Psi> \<turnstile> M \<leftrightarrow> K; set xvec \<subseteq> supp N; length xvec = length Tvec; distinct xvec\<rbrakk> \<Longrightarrow> 
                                       Prop (pInput M xvec N) (K\<lparr>N[xvec::=Tvec]\<rparr>) (P[xvec::=Tvec])"
  and     rOutput: "\<And>M N K. \<Psi> \<turnstile> M \<leftrightarrow> K \<Longrightarrow> Prop (pOutput M N) (K\<langle>N\<rangle>) P"
  and     rTau: "\<Psi> \<rhd> P \<sim> P' \<Longrightarrow> Prop (pTau) (\<tau>) P'"

  shows "Prop \<alpha> \<beta> P'"
using \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<beta> \<prec> P'\<close>
proof(nominal_induct rule: prefix.strong_induct)
  case(pInput M xvec N)
  from \<open>\<Psi> \<rhd> (pInput M xvec N)\<cdot>P \<longmapsto>\<beta> \<prec> P'\<close> have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<beta> \<prec> P'" by simp
  thus ?case by(auto elim: inputCases intro: rInput)
next
  case(pOutput M N)
  from \<open>\<Psi> \<rhd> (pOutput M N)\<cdot>P \<longmapsto>\<beta> \<prec> P'\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<beta> \<prec> P'" by simp
  thus ?case by(auto elim: outputCases intro: rOutput)
next
  case pTau
  from \<open>\<Psi> \<rhd> (pTau)\<cdot>P \<longmapsto>\<beta> \<prec> P'\<close> have "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<beta> \<prec> P'" by simp
  thus ?case
    by(nominal_induct rule: action.strong_induct) (auto dest: tauActionE intro: rTau)
qed  
  
lemma prefixTauCases[consumes 1, case_names cTau]:
  fixes \<alpha>  :: "'a prefix"
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<tau> \<prec> P'"
  and     rTau: "\<Psi> \<rhd> P \<sim> P' \<Longrightarrow> Prop (pTau) P'"

  shows "Prop \<alpha> P'"
proof -
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<tau> \<prec> P'\<close> obtain \<beta> where "\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<beta> \<prec> P'" and "\<beta> = \<tau>" 
    by auto
  thus ?thesis
    by(induct rule: prefixCases) (auto intro: rTau)
qed

lemma hennessySim1:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     C1: "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> Rel"

  shows "\<Psi> \<rhd> \<tau>.(P) \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close>
  obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PChain obtain P'' where "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''" and "\<Psi> \<rhd> P' \<sim> P''"
    by(rule tauChainStepCons)
  thus ?case using P'RelQ' by(metis bisimE C1)
qed

lemma hennessySim2:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     P'RelQ: "(\<Psi>, P', Q) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; \<Psi> \<rhd> Q \<sim> R\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> \<tau>.(Q)"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<tau>.(Q) \<longmapsto>\<tau> \<prec> Q'\<close> have "\<Psi> \<rhd> Q \<sim> Q'" by(blast dest: tauActionE)
  with PTrans P'RelQ show ?case by(metis C1 tauActTauStepChain)
qed

lemma hennessySim3:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     C1: "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> (\<Psi>, P, Q') \<notin> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close>
  obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)
  with C1 \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> show ?case 
    by(force simp add: rtrancl_eq_or_trancl)
qed

lemma tauLaw1SimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto><Rel> Q"
  and     "eqvt Rel"
  and     C1: "\<And>\<Psi> P Q R. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> Rel"

  shows "\<Psi> \<rhd> \<tau>.(P) \<leadsto><Rel> Q"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> Q')
  from \<open>bn \<alpha> \<sharp>* (\<tau>.(P))\<close> have "bn \<alpha> \<sharp>* P" by simp
  with \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>\<alpha> \<noteq> \<tau>\<close>
  obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''" and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                  and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PTrans \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> obtain P''' where "\<Psi> : Q \<rhd> \<tau>.(P) \<Longrightarrow>\<alpha> \<prec> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''"
    by(rule weakTransitionTau)
  moreover from \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> have "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<sim> P'''" by(rule bisimE)
  with P''Chain obtain P'''' where "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''''" and "\<Psi> \<otimes> \<Psi>' \<rhd> P' \<sim> P''''"
    by(rule tauChainBisim)
  ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel\<close> by(metis bisimE C1)
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> P \<leadsto><Rel> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close>
  obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakSimE)

  from PChain obtain P'' where "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "\<Psi> \<rhd> P' \<sim> P''"
    by(rule tauChainCons)
  thus ?case using P'RelQ' by(metis bisimE C1)  
qed

lemma tauLaw1SimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     "(\<Psi>, P, Q) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; \<Psi> \<rhd> Q \<sim> R\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto><Rel> \<tau>.(Q)"
using \<open>eqvt Rel\<close>
proof(induct rule: weakSimI[where C=Q])
  case(cAct \<Psi>' \<alpha> Q')
  hence False by(cases rule: actionCases[where \<alpha>=\<alpha>]) auto
  thus ?case by simp
next
  case(cTau Q')
  have "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" by simp
  moreover from \<open>\<Psi> \<rhd> \<tau>.(Q) \<longmapsto>\<tau> \<prec> Q'\<close> have "\<Psi> \<rhd> Q \<sim> Q'" by(rule tauActionE)
  with \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi>, P, Q') \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma tauLaw3SimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"

  assumes "eqvt Rel"
  and     "(\<Psi>, P, Q) \<in> Rel"
  and     Subst: "\<And>xvec Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"
  and     rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<leadsto><Rel> \<alpha>\<cdot>Q"
using \<open>eqvt Rel\<close>
proof(induct rule: weakSimI[where C=Q])
  case(cAct \<Psi>' \<beta> Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>Q \<longmapsto>\<beta> \<prec> Q'\<close> \<open>\<beta> \<noteq> \<tau>\<close> show ?case
  proof(induct rule: prefixCases)
    case(cInput M xvec N K Tvec)
    note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
    moreover have "insertAssertion (extractFrame(M\<lparr>\<lambda>*xvec N\<rparr>.Q)) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by auto
    ultimately have "\<Psi> : (M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P))) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P))[xvec::=Tvec]" 
      by(rule weakInput)
    hence "\<Psi> : (M\<lparr>\<lambda>*xvec N\<rparr>.Q) \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P))) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> \<tau>.(P[xvec::=Tvec])"
      using \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close>
      by simp
      
    moreover obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P[xvec::=Tvec]) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<otimes> \<Psi>' \<rhd> (P[xvec::=Tvec]) \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P[xvec::=Tvec]) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
    moreover from \<open>length xvec = length Tvec\<close> have "(\<Psi>, P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel" by(rule Subst)
    hence "(\<Psi> \<otimes> \<Psi>', P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel" by(rule rExt)
    with \<open>\<Psi> \<otimes> \<Psi>' \<rhd> P[xvec::=Tvec] \<sim> P'\<close> have "(\<Psi> \<otimes> \<Psi>', P', Q[xvec::=Tvec]) \<in> Rel" by(blast intro: bisimE C1 bisimReflexive)
    ultimately show ?case by fastforce
  next
    case(cOutput M N K)
    note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close>
    moreover have "insertAssertion (extractFrame (M\<langle>N\<rangle>.Q)) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by auto
    ultimately have "\<Psi> : M\<langle>N\<rangle>.Q \<rhd> M\<langle>N\<rangle>.(\<tau>.(P)) \<Longrightarrow>K\<langle>N\<rangle> \<prec> \<tau>.(P)" by(rule weakOutput)
    moreover obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
    moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule rExt)
    with \<open>\<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> P'\<close> have "(\<Psi> \<otimes> \<Psi>', P', Q) \<in> Rel" by(blast intro: bisimE C1 bisimReflexive)
    ultimately show ?case by fastforce
  next
    case cTau
    with \<open>\<tau> \<noteq> \<tau>\<close> show ?case
      by simp
  qed
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>Q \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where tPTrans: "\<Psi> \<rhd> \<tau>.(\<tau>.(P)) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> \<tau>.(P) \<sim> P'" using tauActionI
      by auto
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    from PTrans \<open>\<Psi> \<rhd> \<tau>.(P) \<sim> P'\<close> obtain P''' where P'Trans: "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''"
      apply(drule_tac bisimE(4))
      apply(drule_tac bisimE(2))
      apply(drule_tac simE, auto)
      by(metis bisimE)
    from tPTrans P'Trans have "\<Psi> \<rhd> \<tau>.(\<tau>.(P)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" by(fastforce dest: tauActTauChain)
    moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> \<open>\<Psi> \<rhd> Q \<sim> Q'\<close> have "(\<Psi>, P''', Q') \<in> Rel"
      by(metis bisimTransitive C1 bisimSymmetric)
    ultimately show ?case by fastforce
  qed
qed

lemma tauLaw3SimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "eqvt Rel"
  and     Subst: "\<And>\<Psi> xvec Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], \<tau>.(Q[xvec::=Tvec])) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"
  and     "\<And>\<Psi>. (\<Psi>, P, \<tau>.(Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<leadsto><Rel> \<alpha>\<cdot>(\<tau>.(Q))"
using \<open>eqvt Rel\<close>
proof(induct rule: weakSimI[where C=Q])
  case(cAct \<Psi>' \<beta> Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(Q)) \<longmapsto>\<beta> \<prec> Q'\<close> \<open>\<beta> \<noteq> \<tau>\<close>
  show ?case
  proof(induct rule: prefixCases)
    case(cInput M xvec N K Tvec)
    note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec=length Tvec\<close>
    moreover have "insertAssertion (extractFrame (M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(Q)))) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by auto
    ultimately have "\<Psi> : (M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(Q))) \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
      by(rule weakInput)
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P[xvec::=Tvec] \<Longrightarrow>\<^sup>^\<^sub>\<tau> P[xvec::=Tvec]" by auto
    ultimately show ?case using Subst \<open>length xvec=length Tvec\<close> \<open>distinct xvec\<close>
      by fastforce
  next
    case(cOutput M N K)
    note \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close>
    moreover have "insertAssertion (extractFrame (M\<langle>N\<rangle>.(\<tau>.(Q)))) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by auto
    ultimately have "\<Psi> : M\<langle>N\<rangle>.(\<tau>.(Q)) \<rhd> M\<langle>N\<rangle>.P \<Longrightarrow>K\<langle>N\<rangle> \<prec> P" by(rule weakOutput)
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P" by auto
    ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', P, \<tau>.(Q)) \<in> Rel\<close> by fastforce
  next
    case cTau
    with \<open>\<tau> \<noteq> \<tau>\<close> show ?case by simp
  qed
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(Q)) \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> P \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
    moreover from \<open>\<Psi> \<rhd> P \<sim> P'\<close> \<open>\<Psi> \<rhd> \<tau>.(Q) \<sim> Q'\<close>  \<open>(\<Psi>, P, \<tau>.(Q)) \<in> Rel\<close>
    have "(\<Psi>, P', Q') \<in> Rel" by(metis bisimTransitive bisimSymmetric C1)
    ultimately show ?case by fastforce
  qed
qed

lemma tauLaw3CongSimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"
  and     rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<alpha>\<cdot>Q"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>Q \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where tPTrans: "\<Psi> \<rhd> \<tau>.(\<tau>.(P)) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> \<tau>.(P) \<sim> P'" using tauActionI
      by auto
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    from PTrans \<open>\<Psi> \<rhd> \<tau>.(P) \<sim> P'\<close> obtain P''' where P'Trans: "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''"
      apply(drule_tac bisimE(4))
      apply(drule_tac bisimE(2))
      apply(drule_tac simE, auto)
      by(metis bisimE)
    from tPTrans P'Trans have "\<Psi> \<rhd> \<tau>.(\<tau>.(P)) \<Longrightarrow>\<^sub>\<tau> P'''" by(fastforce dest: tauActTauStepChain)
    moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> \<open>\<Psi> \<rhd> Q \<sim> Q'\<close> have "(\<Psi>, P''', Q') \<in> Rel"
      by(metis bisimTransitive C1 bisimSymmetric)
    ultimately show ?case by fastforce
  qed
qed

lemma tauLaw3CongSimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"
  and     "\<And>\<Psi>. (\<Psi>, P, \<tau>.(Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<leadsto>\<guillemotleft>Rel\<guillemotright> \<alpha>\<cdot>(\<tau>.(Q))"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(Q)) \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> P \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauActTauStepChain)
    moreover from \<open>\<Psi> \<rhd> P \<sim> P'\<close> \<open>\<Psi> \<rhd> \<tau>.(Q) \<sim> Q'\<close>  \<open>(\<Psi>, P, \<tau>.(Q)) \<in> Rel\<close>
    have "(\<Psi>, P', Q') \<in> Rel" by(metis bisimTransitive bisimSymmetric C1)
    ultimately show ?case by fastforce
  qed
qed

end

locale tauSum = tau + sum
begin

lemma tauLaw2SimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes Id: "\<And>\<Psi> P. (\<Psi>, P, P) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<leadsto><Rel> \<tau>.(P)"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> P')
  thus ?case by(nominal_induct \<alpha> rule: action.strong_inducts) auto
next
  case(cTau P')
  from \<open>\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close> have "\<Psi> \<rhd> P \<sim> P'" by(rule tauActionE)
  obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
    by auto
  have "guarded(\<tau>.(P))" by(rule guardedTau)
  with PTrans have "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" by(rule Sum2)
  hence "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(rule tauActTauChain)
  moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>(\<Psi>, P, P) \<in> Rel\<close> \<open>\<Psi> \<rhd> P \<sim> P'\<close> have "(\<Psi>, P'', P') \<in> Rel"
    by(metis C1 bisimE)
  ultimately show ?case by blast
qed  

lemma tauLaw2CongSimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes Id: "\<And>\<Psi> P. (\<Psi>, P, P) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q R S. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; (\<Psi>, Q, R) \<in> Rel; \<Psi> \<rhd> R \<sim> S\<rbrakk> \<Longrightarrow> (\<Psi>, P, S) \<in> Rel"

  shows "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<tau>.(P)"
proof(induct rule: weakCongSimI)
  case(cTau P')
  from \<open>\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close> have "\<Psi> \<rhd> P \<sim> P'" by(rule tauActionE)
  obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
    by auto
  have "guarded(\<tau>.(P))" by(rule guardedTau)
  with PTrans have "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" by(rule Sum2)
  hence "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''" by(rule tauActTauStepChain)
  moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>(\<Psi>, P, P) \<in> Rel\<close> \<open>\<Psi> \<rhd> P \<sim> P'\<close> have "(\<Psi>, P'', P') \<in> Rel"
    by(metis C1 bisimE)
  ultimately show ?case by blast
qed  

lemma tauLaw2SimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<tau>.(P) \<leadsto><Rel> P \<oplus> \<tau>.(P)"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> P')
  from \<open>\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<longmapsto>\<alpha> \<prec> P'\<close>
  show ?case
  proof(induct rule: sumCases)
    case cSum1 
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    from PTrans have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(rule tauActTauChain)
    moreover from \<open>guarded P\<close> have "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
      by(rule insertGuardedAssertion)
    with \<open>\<Psi> \<rhd> P \<sim> P''\<close> have "insertAssertion (extractFrame P'') \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
      by(metis bisimE FrameStatEqTrans FrameStatEqSym)
    hence "insertAssertion (extractFrame(P \<oplus> \<tau>.(P))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
      by(simp add: FrameStatEq_def)
    moreover from PTrans \<open>bn \<alpha> \<sharp>* (\<tau>.(P))\<close> have "bn \<alpha> \<sharp>* P''" by(rule tauFreshChainDerivative)
    with \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    obtain P''' where P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'''" and "\<Psi> \<rhd> P''' \<sim> P'"
      by(metis bisimE simE)
    ultimately have "\<Psi> : (P \<oplus> \<tau>.(P)) \<rhd> \<tau>.(P) \<Longrightarrow>\<alpha> \<prec> P'''"
      by(rule_tac weakTransitionI)
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" by auto
    moreover from \<open>\<Psi> \<rhd> P''' \<sim> P'\<close> have "\<Psi> \<otimes> \<Psi>' \<rhd> P''' \<sim> P'" by(rule bisimE)
    hence "(\<Psi> \<otimes> \<Psi>', P''', P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case cSum2
    thus ?case using \<open>\<alpha> \<noteq> \<tau>\<close>
      by(nominal_induct \<alpha> rule: action.strong_inducts) auto
  qed
next
  case(cTau P')
  from \<open>\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close>
  show ?case
  proof(induct rule: sumCases)
    case cSum1 
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'\<close> 
    obtain P''' where P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P''' \<sim> P'"
      apply(drule_tac bisimE(4))
      apply(drule_tac bisimE(2))
      by(drule_tac simE, auto)
    ultimately have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" by(auto dest: tauActTauChain rtrancl_into_rtrancl)
    moreover from \<open>\<Psi> \<rhd> P''' \<sim> P'\<close> have "(\<Psi>, P''', P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case cSum2
    from \<open>\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close> have "\<Psi> \<rhd> P \<sim> P'" by(rule tauActionE)
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    hence "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(rule_tac tauActTauChain)
    moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P \<sim> P'\<close> have "(\<Psi>, P'', P') \<in> Rel"
      by(metis C1 bisimTransitive bisimE)
    ultimately show ?case by blast
  qed
qed

lemma tauLaw2CongSimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<tau>.(P) \<leadsto>\<guillemotleft>Rel\<guillemotright> P \<oplus> \<tau>.(P)"
proof(induct rule: weakCongSimI)
  case(cTau P')
  from \<open>\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close>
  show ?case
  proof(induct rule: sumCases)
    case cSum1 
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'\<close> 
    obtain P''' where P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P''' \<sim> P'"
      apply(drule_tac bisimE(4))
      apply(drule_tac bisimE(2))
      by(drule_tac simE) auto
    ultimately have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''" by(auto dest: tauActTauStepChain trancl_into_trancl)
    moreover from \<open>\<Psi> \<rhd> P''' \<sim> P'\<close> have "(\<Psi>, P''', P') \<in> Rel" by(rule C1)
    ultimately show ?case by blast
  next
    case cSum2
    from \<open>\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'\<close> have "\<Psi> \<rhd> P \<sim> P'" by(rule tauActionE)
    obtain P'' where PTrans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
      by auto
    hence "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P''" by(rule_tac tauActTauStepChain)
    moreover from \<open>\<Psi> \<rhd> P \<sim> P''\<close> \<open>\<Psi> \<rhd> P \<sim> P'\<close> have "(\<Psi>, P'', P') \<in> Rel"
      by(metis C1 bisimTransitive bisimE)
    ultimately show ?case by blast
  qed
qed

lemma tauLaw4SimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a

  assumes "\<And>\<Psi> P. (\<Psi>, P, P) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto><Rel> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<beta> PQ)
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<longmapsto>\<beta> \<prec> PQ\<close> \<open>\<beta> \<noteq> \<tau>\<close>
  show ?case
  proof(induct rule: prefixCases)
    case(cInput M xvec N K Tvec)
    have "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
    moreover have "insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi>"
      using insertTauAssertion Identity
      by(nominal_induct \<alpha> rule: prefix.strong_inducts, auto) 
        (rule FrameStatImpTrans[where G="\<langle>\<epsilon>, \<Psi>\<rangle>"], auto simp add: FrameStatEq_def AssertionStatEq_def)
    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec=length Tvec\<close>
    have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]"
      by(rule Input)
    hence "\<Psi> \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]" 
      by(rule_tac Sum2) auto
    ultimately have "\<Psi> : (M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)) \<rhd> (M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]"
      by(rule_tac weakTransitionI) auto
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec] \<Longrightarrow>\<^sup>^\<^sub>\<tau> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]" by auto
    ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', (\<tau>.(P) \<oplus> Q)[xvec::=Tvec], (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]) \<in> Rel\<close> by fastforce
  next
    case(cOutput M N K)
    have "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
    moreover have "insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi>"
      using insertTauAssertion Identity
      by(nominal_induct \<alpha> rule: prefix.strong_inducts, auto) 
        (rule FrameStatImpTrans[where G="\<langle>\<epsilon>, \<Psi>\<rangle>"], auto simp add: FrameStatEq_def AssertionStatEq_def)

    moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)"
      by(rule Output)
    hence "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)" by(rule_tac Sum2) auto
    ultimately have "\<Psi> : (M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)"
      by(rule_tac weakTransitionI) auto
    moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<oplus> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<tau>.(P) \<oplus> Q" by auto
    ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', \<tau>.(P) \<oplus> Q, \<tau>.(P) \<oplus> Q) \<in> Rel\<close> by fastforce
  next
    case cTau
    from \<open>\<tau> \<noteq> \<tau>\<close> show ?case
      by simp
  qed
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<oplus>\<^sub>\<top> Q \<longmapsto> \<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> \<tau>.(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" by(rule_tac Sum2) (auto intro: guardedTau)
    hence "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> \<tau>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
    moreover from \<open>\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> P'\<close> \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> Q'\<close> have "\<Psi> \<rhd> P' \<sim> Q'" by(metis bisimSymmetric bisimTransitive)
    hence "(\<Psi>, P', Q') \<in> Rel" by(rule C1)
    ultimately show ?case by fastforce
  qed
qed

lemma tauLaw4CongSimLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a

  assumes "\<And>\<Psi> P. (\<Psi>, P, P) \<in> Rel"
  and     C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<oplus>\<^sub>\<top> Q \<longmapsto> \<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: prefixTauCases)
    case cTau
    obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> P'" using tauActionI
      by auto
    from PTrans have "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> \<tau>.(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" by(rule_tac Sum2) (auto intro: guardedTau)
    hence "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> \<tau>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauActTauStepChain)
    moreover from \<open>\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> P'\<close> \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> Q'\<close> have "\<Psi> \<rhd> P' \<sim> Q'" by(metis bisimSymmetric bisimTransitive)
    hence "(\<Psi>, P', Q') \<in> Rel" by(rule C1)
    ultimately show ?case by fastforce
  qed
qed

lemma tauLaw4SimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"

  assumes C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"
  and         "\<And>\<Psi> P. (\<Psi>, P, P) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto><Rel> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<beta> PQ)
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<longmapsto>\<beta> \<prec> PQ\<close> show ?case
  proof(induct rule: sumCases)
    case cSum1
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto>\<beta> \<prec> PQ\<close> \<open>\<beta> \<noteq> \<tau>\<close> show ?case
    proof(induct rule: prefixCases)
      case(cInput M xvec N K Tvec)
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)" by auto
      moreover have "insertAssertion (extractFrame((M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q))) \<Psi>"
        by auto
      moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]" by(rule Input)
      ultimately have "\<Psi> : ((M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr>\<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]"
        by(rule_tac weakTransitionI) auto
      with \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close>
      have "\<Psi> : ((M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P[xvec::=Tvec]) \<oplus> Q[xvec::=Tvec])"
        by auto
      moreover obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P[xvec::=Tvec]) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<otimes> \<Psi>' \<rhd> P[xvec::=Tvec] \<sim> P'" using tauActionI
        by auto
      have "guarded(\<tau>.(P[xvec::=Tvec]))" by(rule guardedTau)
      with PTrans have "\<Psi> \<otimes> \<Psi>' \<rhd> (\<tau>.(P[xvec::=Tvec])) \<oplus> (Q[xvec::=Tvec]) \<longmapsto>\<tau> \<prec> P'" by(rule Sum1)
      hence "\<Psi> \<otimes> \<Psi>' \<rhd> (\<tau>.(P[xvec::=Tvec])) \<oplus> (Q[xvec::=Tvec]) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
      moreover from \<open>\<Psi> \<otimes> \<Psi>' \<rhd> P[xvec::=Tvec] \<sim> P'\<close> have "(\<Psi> \<otimes> \<Psi>', P', P[xvec::=Tvec]) \<in> Rel" by(metis bisimE C1)
      ultimately show ?case by fastforce
    next
      case(cOutput M N K)
      have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q)" by auto
      moreover have "insertAssertion (extractFrame(M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q))) \<Psi>"
        by auto
      moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)" by(rule Output)
      ultimately have "\<Psi> : (M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)"
        by(rule_tac weakTransitionI) auto
      moreover obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> P'" using tauActionI
        by auto
      have "guarded(\<tau>.(P))" by(rule guardedTau)
      with PTrans have "\<Psi> \<otimes> \<Psi>' \<rhd> (\<tau>.(P)) \<oplus> Q \<longmapsto>\<tau> \<prec> P'" by(rule Sum1)
      hence "\<Psi> \<otimes> \<Psi>' \<rhd> (\<tau>.(P)) \<oplus> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
      moreover from \<open>\<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> P'\<close> have "(\<Psi> \<otimes> \<Psi>', P', P) \<in> Rel" by(metis bisimE C1)
      ultimately show ?case by fastforce 
    next
      case cTau
      from \<open>\<tau> \<noteq> \<tau>\<close> show ?case by simp
    qed
  next
    case cSum2
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<longmapsto>\<beta> \<prec> PQ\<close> \<open>\<beta> \<noteq> \<tau>\<close> show ?case
    proof(induct rule: prefixCases)
      case(cInput M xvec N K Tvec)
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)" by auto
      moreover have "insertAssertion (extractFrame((M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q))) \<Psi>"
        by auto
      moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> \<open>distinct xvec\<close> \<open>set xvec \<subseteq> supp N\<close> \<open>length xvec = length Tvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P) \<oplus> Q)[xvec::=Tvec]"
        by(rule Input)
      with \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close>
      have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P[xvec::=Tvec]) \<oplus> Q[xvec::=Tvec])"
        by simp
      ultimately have "\<Psi> : ((M\<lparr>\<lambda>*xvec N\<rparr>.P) \<oplus> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> (\<tau>.(P[xvec::=Tvec]) \<oplus> Q[xvec::=Tvec])"
        by(rule_tac weakTransitionI) auto
      moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P[xvec::=Tvec]) \<oplus> (Q[xvec::=Tvec]) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<tau>.(P[xvec::=Tvec]) \<oplus> (Q[xvec::=Tvec])" by auto
      ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', \<tau>.(P[xvec::=Tvec]) \<oplus> (Q[xvec::=Tvec]), \<tau>.(P[xvec::=Tvec]) \<oplus> (Q[xvec::=Tvec])) \<in> Rel\<close> \<open>length xvec = length Tvec\<close> \<open>distinct xvec\<close>
        by fastforce
    next
      case(cOutput M N K)
      have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q)" by auto
      moreover have "insertAssertion (extractFrame(M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q))) \<Psi>"
        by auto
      moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<longmapsto>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)"
        by(rule Output)
      ultimately have "\<Psi> : (M\<langle>N\<rangle>.P \<oplus> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q)) \<rhd> M\<langle>N\<rangle>.(\<tau>.(P) \<oplus> Q) \<Longrightarrow>K\<langle>N\<rangle> \<prec> (\<tau>.(P) \<oplus> Q)"
        by(rule_tac weakTransitionI) auto
      moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<oplus> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<tau>.(P) \<oplus> Q" by auto
      ultimately show ?case using \<open>(\<Psi> \<otimes> \<Psi>', \<tau>.(P) \<oplus> Q, \<tau>.(P) \<oplus> Q) \<in> Rel\<close> by fastforce
    next
      case cTau
      from \<open>\<tau> \<noteq> \<tau>\<close> show ?case by simp
    qed
  qed
next
  case(cTau PQ)
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> PQ\<close> show ?case
  proof(induct rule: sumCases)
    case cSum1
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto> \<tau> \<prec> PQ\<close> show ?case
    proof(induct rule: prefixTauCases)
      case cTau
      obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'" using tauActionI
        by auto
      obtain P'' where P'Trans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
        by auto
      from P'Trans have "\<Psi> \<rhd> \<tau>.(P) \<oplus> Q\<longmapsto>\<tau> \<prec> P''" by(rule_tac Sum1) (auto intro: guardedTau)
      with \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'\<close> obtain P''' where P''Trans: "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''"
        apply(drule_tac bisimE(4))
        apply(drule_tac bisimE(2))
        apply(drule_tac simE)
        by(auto dest: bisimE)
      from PTrans P''Trans have "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''" by(fastforce dest: tauActTauChain)
      moreover from \<open>\<Psi> \<rhd> P \<sim> PQ\<close> \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> \<open>\<Psi> \<rhd> P \<sim> P''\<close> have "\<Psi> \<rhd> P''' \<sim> PQ"
        by(metis bisimSymmetric bisimTransitive)
      hence "(\<Psi>, P''', PQ) \<in> Rel" by(rule C1)
      ultimately show ?case by fastforce
    qed
  next
    case cSum2
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> PQ\<close> show ?case
    proof(induct rule: prefixTauCases)
      case cTau
      obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'" using tauActionI
        by auto
      from PTrans have "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauActTauChain)
      moreover from \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'\<close> \<open>\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> PQ\<close> have "\<Psi> \<rhd> P' \<sim> PQ"
        by(metis bisimSymmetric bisimTransitive)
      hence "(\<Psi>, P', PQ) \<in> Rel" by(rule C1)
      ultimately show ?case by fastforce
    qed
  qed
qed

lemma tauLaw4CongSimRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"

  assumes C1: "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<sim> Q \<Longrightarrow> (\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakCongSimI)
  case(cTau PQ)
  from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<longmapsto>\<tau> \<prec> PQ\<close> show ?case
  proof(induct rule: sumCases)
    case cSum1
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>P \<longmapsto> \<tau> \<prec> PQ\<close> show ?case
    proof(induct rule: prefixTauCases)
      case cTau
      obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'" using tauActionI
        by auto
      obtain P'' where P'Trans: "\<Psi> \<rhd> \<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and "\<Psi> \<rhd> P \<sim> P''" using tauActionI
        by auto
      from P'Trans have "\<Psi> \<rhd> \<tau>.(P) \<oplus> Q\<longmapsto>\<tau> \<prec> P''" by(rule_tac Sum1) (auto intro: guardedTau)
      with \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'\<close> obtain P''' where P''Trans: "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P'''" and "\<Psi> \<rhd> P'' \<sim> P'''"
        apply(drule_tac bisimE(4))
        apply(drule_tac bisimE(2))
        apply(drule_tac simE)
        by(auto dest: bisimE)
      from PTrans P''Trans have "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<Longrightarrow>\<^sub>\<tau> P'''" by(fastforce dest: tauActTauStepChain)
      moreover from \<open>\<Psi> \<rhd> P \<sim> PQ\<close> \<open>\<Psi> \<rhd> P'' \<sim> P'''\<close> \<open>\<Psi> \<rhd> P \<sim> P''\<close> have "\<Psi> \<rhd> P''' \<sim> PQ"
        by(metis bisimSymmetric bisimTransitive)
      hence "(\<Psi>, P''', PQ) \<in> Rel" by(rule C1)
      ultimately show ?case by fastforce
    qed
  next
    case cSum2
    from \<open>\<Psi> \<rhd> \<alpha>\<cdot>((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> PQ\<close> show ?case
    proof(induct rule: prefixTauCases)
      case cTau
      obtain P' where PTrans: "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<longmapsto>\<tau> \<prec> P'" and "\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'" using tauActionI
        by auto
      from PTrans have "\<Psi> \<rhd> \<tau>.((\<tau>.(P)) \<oplus> Q) \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauActTauStepChain)
      moreover from \<open>\<Psi> \<rhd> (\<tau>.(P)) \<oplus> Q \<sim> P'\<close> \<open>\<Psi> \<rhd> \<tau>.(P) \<oplus> Q \<sim> PQ\<close> have "\<Psi> \<rhd> P' \<sim> PQ"
        by(metis bisimSymmetric bisimTransitive)
      hence "(\<Psi>, P', PQ) \<in> Rel" by(rule C1)
      ultimately show ?case by fastforce
    qed
  qed
qed

end

end
