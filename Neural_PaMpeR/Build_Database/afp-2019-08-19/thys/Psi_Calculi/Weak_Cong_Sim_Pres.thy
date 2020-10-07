(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Sim_Pres
  imports Weak_Sim_Pres Weak_Cong_Simulation
begin

context env begin

lemma caseWeakSimPres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> Eq \<Psi> P Q"
  and     Sim:   "\<And>\<Psi>' P Q. (\<Psi>', P, Q) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> P \<leadsto><Rel> Q"
  and     EqRel: "\<And>\<Psi>' P Q. Eq \<Psi>' P Q \<Longrightarrow> (\<Psi>', P, Q) \<in> Rel"
  and     EqSim: "\<And>\<Psi>' P Q. Eq \<Psi>' P Q \<Longrightarrow> \<Psi>' \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "\<Psi> \<rhd> Cases CsP \<leadsto><Rel> Cases CsQ"
proof(induct rule: weakSimI2)
  case(cAct \<Psi>' \<alpha> Q')
  from \<open>bn \<alpha> \<sharp>* (Cases CsP)\<close> have "bn \<alpha> \<sharp>* CsP" by auto
  from \<open>\<Psi> \<rhd> Cases CsQ \<longmapsto>\<alpha> \<prec> Q'\<close>
  show ?case
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from \<open>(\<phi>, Q) mem CsQ\<close> obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "Eq \<Psi> P Q"
      by(metis PRelQ)
    from \<open>Eq \<Psi> P Q\<close> have "\<Psi> \<rhd> P \<leadsto><Rel> Q" by(metis EqRel Sim)
    moreover note \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    moreover from \<open>bn \<alpha> \<sharp>* CsP\<close> \<open>(\<phi>, P) mem CsP\<close> have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
    ultimately obtain P'' P' where PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P''"
                               and P''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>', P', Q') \<in> Rel"
      using \<open>\<alpha> \<noteq> \<tau>\<close>
      by(blast dest: weakSimE)
    note PTrans \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close>
    moreover from \<open>guarded Q\<close> have "insertAssertion (extractFrame Q) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
      by(rule insertGuardedAssertion)
    hence "insertAssertion (extractFrame(Cases CsQ)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
      by(auto simp add: FrameStatEq_def)
    moreover from Identity have "insertAssertion (extractFrame(Cases CsQ)) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
      by(auto simp add: AssertionStatEq_def)
    ultimately have "\<Psi> : (Cases CsQ) \<rhd> Cases CsP \<Longrightarrow>\<alpha> \<prec> P''"
      by(rule weakCase)
    with P''Chain P'RelQ' show ?case by blast
  qed
next
  case(cTau Q')
  from \<open>\<Psi> \<rhd> Cases CsQ \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from \<open>(\<phi>, Q) mem CsQ\<close> obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "Eq \<Psi> P Q"
      by(metis PRelQ)
    from \<open>Eq \<Psi> P Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close>
    obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: EqSim weakCongSimE)
    from PChain \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P'"
      by(rule tauStepChainCase)
    hence "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(simp add: trancl_into_rtrancl)
    with P'RelQ' show ?case by blast
  qed
qed

lemma weakCongSimCasePres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> Eq \<Psi> P Q"
  and     EqSim: "\<And>\<Psi>' P Q. Eq \<Psi>' P Q \<Longrightarrow> \<Psi>' \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "\<Psi> \<rhd> Cases CsP \<leadsto>\<guillemotleft>Rel\<guillemotright> Cases CsQ"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> Cases CsQ \<longmapsto>\<tau> \<prec> Q'\<close> show ?case
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from \<open>(\<phi>, Q) mem CsQ\<close> obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "Eq \<Psi> P Q"
      by(metis PRelQ)
    from \<open>Eq \<Psi> P Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close>
    obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: EqSim weakCongSimE)
    from PChain \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P'"
      by(rule tauStepChainCase)
    with P'RelQ' show ?case by blast
  qed
qed

lemma weakCongSimResPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     "eqvt Rel'"
  and     "x \<sharp> \<Psi>"
  and     "Rel \<subseteq> Rel'"
  and     C1: "\<And>\<Psi>' R S x. \<lbrakk>(\<Psi>', R, S) \<in> Rel; x \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>x\<rparr>R, \<lparr>\<nu>x\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto>\<guillemotleft>Rel'\<guillemotright> \<lparr>\<nu>x\<rparr>Q"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> Q'\<close> have "x \<sharp> Q'" by(auto dest: tauFreshDerivative simp add: abs_fresh) 
  with  \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<tau> \<prec> Q'\<close> \<open>x \<sharp> \<Psi>\<close> show ?case
  proof(induct rule: resTauCases)
    case(cRes Q')
    from PSimQ \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel" 
      by(blast dest: weakCongSimE)
    from PChain \<open>x \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'" by(rule tauStepChainResPres)
    moreover from P'RelQ' \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  qed
qed

lemma weakCongSimResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     C1:    "\<And>\<Psi>' R S xvec. \<lbrakk>(\<Psi>', R, S) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>R, \<lparr>\<nu>*xvec\<rparr>S) \<in> Rel"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>\<guillemotleft>Rel\<guillemotright> \<lparr>\<nu>*xvec\<rparr>Q"
using \<open>xvec \<sharp>* \<Psi>\<close>
proof(induct xvec)
  case Nil
  from PSimQ show ?case by simp
next
  case(Cons x xvec)
  from \<open>(x#xvec) \<sharp>* \<Psi>\<close> have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by simp+
  from \<open>xvec \<sharp>* \<Psi> \<Longrightarrow> \<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>\<guillemotleft>Rel\<guillemotright> \<lparr>\<nu>*xvec\<rparr>Q\<close> \<open>xvec \<sharp>* \<Psi>\<close>
  have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>\<guillemotleft>Rel\<guillemotright> \<lparr>\<nu>*xvec\<rparr>Q" by simp
  moreover note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "Rel \<subseteq> Rel" by simp
  moreover have "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>*[x]\<rparr>P, \<lparr>\<nu>*[x]\<rparr>Q) \<in> Rel"
    by(rule_tac xvec="[x]" in C1) auto
  hence "\<And>\<Psi> P Q x. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; x \<sharp> \<Psi>\<rbrakk> \<Longrightarrow> (\<Psi>, \<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> Rel"
    by simp
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)"
    by(rule weakCongSimResPres)
  thus ?case by simp
qed

lemma weakCongSimParPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes PSimQ: "\<And>\<Psi>'. \<Psi>' \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     PSimQ': "\<And>\<Psi>'. \<Psi>' \<rhd> P \<leadsto><Rel> Q"
  and     StatImp: "\<And>\<Psi>'. \<Psi>' \<rhd> Q \<lessapprox><Rel> P"

  and            "eqvt Rel"
  and            "eqvt Rel'"

  and     Sym:    "\<And>\<Psi>' S T. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     Ext:    "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"

  and     C1: "\<And>\<Psi>' S T A\<^sub>U \<Psi>\<^sub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> R \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q \<parallel> R"
proof(induct rule: weakCongSimI)
  case(cTau QR)
  from \<open>\<Psi> \<rhd> Q \<parallel> R \<longmapsto>\<tau> \<prec> QR\<close> show ?case
  proof(induct rule: parTauCases[where C="(P, R)"])
    case(cPar1 Q' A\<^sub>R \<Psi>\<^sub>R)
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P"
      by simp+
    have FrR: " extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    with \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
      by(rule_tac PSimQ)
    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" by fact
    ultimately obtain P' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
      by(rule weakCongSimE)
    from PChain QTrans \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
      by(force dest: freeFreshChainDerivative tauStepChainFreshChain)+
    from PChain FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sub>\<tau> (P' \<parallel> R)"
      by(rule tauStepChainPar1)
    moreover from P'RelQ' FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>R \<sharp>* Q'\<close> have "(\<Psi>, P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, R)"
      by(rule freshFrame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* R"
      by simp+
    
    have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(drule_tac extractFrameFreshChain) auto
      
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi>, P, Q, A\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, R)" and "distinct A\<^sub>R"
      by(rule freshFrame)
    then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* A\<^sub>Q" and  "A\<^sub>R \<sharp>* A\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P"
          and "A\<^sub>R \<sharp>* R"
      by simp+
    
    from \<open>A\<^sub>Q \<sharp>* R\<close>  FrR \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" by(drule_tac extractFrameFreshChain) auto
    from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> FrR  have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" by(drule_tac extractFrameFreshChain) auto
    
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<tau> \<prec> R'\<close> FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close>
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                         and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, Q, R)" in expandTauFrame) (assumption | simp)+

    from FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
    obtain P' P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                    and QimpP': "insertAssertion(extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                    and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                    and P'RelQ: "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P'', Q) \<in> Rel"
      by(metis StatImp weakStatImp_def Sym)
    obtain A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "A\<^sub>P' \<sharp>* \<Psi>" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q"
                      and "A\<^sub>P' \<sharp>* A\<^sub>Q" and "A\<^sub>P' \<sharp>* R" and "A\<^sub>P' \<sharp>* A\<^sub>R"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, \<Psi>\<^sub>Q, A\<^sub>Q, R, A\<^sub>R)" in freshFrame) auto

    from PChain P'Chain \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* P'" and "A\<^sub>R \<sharp>* P'" and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* P''"
      by(force intro: tauChainFreshChain)+
    from \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>Q\<close> FrP' have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P'"
      by(force dest: extractFrameFreshChain)+
      
    from PChain FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R" by(rule tauChainPar1)
    moreover have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P' \<rhd> R \<longmapsto>\<tau> \<prec> R'"
    proof -
      have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<tau> \<prec> R'" by fact
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
      proof -
        have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
          by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym FrameStatEqSym)
        moreover with FrP' FrQ QimpP' \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
        have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle>" using freshCompChain
          by simp
        moreover have "\<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P', (\<Psi> \<otimes> \<Psi>\<^sub>P') \<otimes> \<Psi>\<^sub>R\<rangle>"
          by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym frameIntAssociativity[THEN FrameStatEqSym])
        ultimately show ?thesis
          by(rule FrameStatEqImpCompose)
      qed
      ultimately show ?thesis
        using \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'\<close> \<open>A\<^sub>P' \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> 
              \<open>A\<^sub>P' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P'\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P'\<close> FrR \<open>distinct A\<^sub>R\<close>
        by(force intro: transferTauFrame)
    qed
    hence "\<Psi> \<rhd> P' \<parallel> R \<longmapsto>\<tau> \<prec> (P' \<parallel> R')" using FrP' \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P' \<sharp>* R\<close>
      by(rule_tac Par2) auto
    moreover from P'Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
      by(metis tauChainStatEq Associativity)
    with \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" 
      by(rule_tac tauChainStatEq, auto) (metis compositionSym)
    hence "\<Psi> \<rhd> P' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> R'" using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> by(rule_tac tauChainPar1)
    ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sub>\<tau> (P'' \<parallel> R')"
      by(drule_tac tauActTauStepChain) auto
    
    moreover from P'RelQ \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P'', Q) \<in> Rel" by(blast intro: C3 Associativity compositionSym)
    with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P''\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> have "(\<Psi>, P'' \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) 
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    
    have  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+
    from \<open>xvec \<sharp>* (P, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
    
    have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow>K" by fact+

    from RTrans FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
                    \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close>
                     \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
    obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                           and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                           and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* K" and "(p \<bullet> xvec) \<sharp>* R"
                           and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* N"
      by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>Q)"  and C'="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>Q)" in expandFrame) (assumption | simp)+

    from \<open>A\<^sub>R \<sharp>* \<Psi>\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
    from \<open>A\<^sub>R \<sharp>* P\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
    from \<open>A\<^sub>R \<sharp>* Q\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp
    from \<open>A\<^sub>R \<sharp>* R\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> R)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>xvec \<sharp>* R\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* R" by simp
    from \<open>A\<^sub>R \<sharp>* K\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> K)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>xvec \<sharp>* K\<close> \<open>(p \<bullet> xvec) \<sharp>* K\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* K" by simp
    
    from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by(simp add: freshChainSimps)
    from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> S have "A\<^sub>Q \<sharp>* (p \<bullet> A\<^sub>R)" by(simp add: freshChainSimps)
    
    from QTrans S \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
      by(rule_tac inputPermFrameSubject) (assumption | auto simp add: fresh_star_def)+
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S have QTrans: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
      by(simp add: eqvts)
    from FrR have "(p \<bullet> extractFrame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
    with \<open>xvec \<sharp>* R\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have FrR: "extractFrame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(simp add: eqvts)
    
    from MeqK have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R)) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)" by(rule chanEqClosed)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* K\<close> \<open>(p \<bullet> xvec) \<sharp>* K\<close> S
    have MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K" by(simp add: eqvts)
    
    have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<leadsto><Rel> Q" by(rule PSimQ')

    with QTrans obtain P' P'' where PTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P''"
                                and P''Chain: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                                and P'RelQ': "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P', Q') \<in> Rel"
      by(fastforce dest: weakSimE)
    from PTrans QTrans \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>A\<^sub>R' \<sharp>* N\<close> have "A\<^sub>R' \<sharp>* P''" and "A\<^sub>R' \<sharp>* Q'"
      by(blast dest: weakInputFreshChainDerivative inputFreshChainDerivative)+

    from PTrans obtain P''' where PChain: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''"
                              and QimpP''': "insertAssertion (extractFrame Q) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P''') (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))"
                              and P'''Trans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P''' \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P''"
      by(rule weakTransitionE)
    
    from PChain \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* P\<close> have "xvec \<sharp>* P'''" and "(p \<bullet> A\<^sub>R) \<sharp>* P'''" and "A\<^sub>R' \<sharp>* P'''"
      by(force intro: tauChainFreshChain)+
    from P'''Trans \<open>A\<^sub>R' \<sharp>* P'''\<close> \<open>A\<^sub>R' \<sharp>* N\<close> have "A\<^sub>R' \<sharp>* P''" by(force dest: inputFreshChainDerivative)
    
    obtain A\<^sub>P''' \<Psi>\<^sub>P''' where FrP''': "extractFrame P''' = \<langle>A\<^sub>P''', \<Psi>\<^sub>P'''\<rangle>" and "A\<^sub>P''' \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, p \<bullet> A\<^sub>R, p \<bullet> \<Psi>\<^sub>R, p \<bullet> M, N, K, R, P''', xvec)" and "distinct A\<^sub>P'''"
      by(rule freshFrame)
    hence "A\<^sub>P''' \<sharp>* \<Psi>" and "A\<^sub>P''' \<sharp>* A\<^sub>Q" and "A\<^sub>P''' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P''' \<sharp>* (p \<bullet> M)" and "A\<^sub>P''' \<sharp>* R"
      and "A\<^sub>P''' \<sharp>* N" and "A\<^sub>P''' \<sharp>* K" and "A\<^sub>P''' \<sharp>* (p \<bullet> A\<^sub>R)" and "A\<^sub>P''' \<sharp>* P'''" and "A\<^sub>P''' \<sharp>* xvec" and "A\<^sub>P''' \<sharp>* (p \<bullet> \<Psi>\<^sub>R)"
      by simp+

    have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    moreover with QimpP''' FrP''' FrQ \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* (p \<bullet> \<Psi>\<^sub>R)\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> S
    have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P'''\<rangle>" using freshCompChain
      by(simp add: freshChainSimps)
    moreover have "\<langle>A\<^sub>P''', (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P'''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    ultimately have QImpP''': "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(rule FrameStatEqImpCompose)
      
    from PChain FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''' \<parallel> R" by(rule tauChainPar1)
    moreover from RTrans FrR P'''Trans MeqK QImpP''' FrP''' FrQ \<open>distinct A\<^sub>P'''\<close> \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>P''' \<sharp>* (p \<bullet> A\<^sub>R)\<close> \<open>A\<^sub>Q \<sharp>* (p \<bullet> A\<^sub>R)\<close>
      \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P'''\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K\<close> \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* R\<close>
      \<open>A\<^sub>P''' \<sharp>* P'''\<close> \<open>A\<^sub>P''' \<sharp>* (p \<bullet> M)\<close> \<open>A\<^sub>Q \<sharp>* R\<close>  \<open>A\<^sub>Q \<sharp>* (p \<bullet> M)\<close> 
    obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K'" and "(p \<bullet> A\<^sub>R) \<sharp>* K'"
      by(rule_tac comm1Aux) (assumption | simp)+
    
    with P'''Trans FrP''' have "\<Psi> \<rhd> P''' \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R')" using FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P'''\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close>
      \<open>xvec \<sharp>* P'''\<close> \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* P'''\<close> \<open>A\<^sub>P''' \<sharp>* R\<close> \<open>A\<^sub>P''' \<sharp>* (p \<bullet> M)\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K'\<close> \<open>A\<^sub>P''' \<sharp>* (p \<bullet> A\<^sub>R)\<close>
      by(rule_tac Comm1)
    
    moreover from P''Chain \<open>A\<^sub>R' \<sharp>* P''\<close> have "A\<^sub>R' \<sharp>* P'" by(rule tauChainFreshChain)
    from \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>R'"
      by(metis Associativity AssertionStatEqTrans AssertionStatEqSym compositionSym)
    with P''Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauChainStatEq)
    hence "\<Psi> \<rhd> P'' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R'" using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P''\<close> by(rule tauChainPar1)
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R') \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using \<open>xvec \<sharp>* \<Psi>\<close> by(rule tauChainResChainPres)
    ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')"
      by(drule_tac tauActTauStepChain) auto
    moreover from P'RelQ' \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel"  by(metis C3 Associativity compositionSym)
    with FrR' \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
    with \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'"
      by(rule_tac C2)
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    
    have  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+
    from \<open>xvec \<sharp>* (P, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
    
    have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'"
     and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow>K" by fact+

    from RTrans FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* Q'\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* K\<close>
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where  ReqR': "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" 
                         and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q'" and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* xvec"
      by(rule_tac C="(\<Psi>, P, Q', N, xvec)" and C'="(\<Psi>, P, Q', N, xvec)" in expandFrame) auto
    
    have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto><Rel> Q" by(rule PSimQ')
    
    with QTrans \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>R\<close> \<open>xvec \<sharp>* P\<close>
    obtain P'' P' where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
                    and P''Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
                    and P'RelQ': "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', Q') \<in> Rel"
      by(fastforce dest: weakSimE)

    from PTrans obtain P''' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''"
                              and QimpP''': "insertAssertion (extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P''') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                              and P'''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P''' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P''"
      by(rule weakTransitionE)
      
    from PChain \<open>A\<^sub>R \<sharp>* P\<close> have "A\<^sub>R \<sharp>* P'''" by(rule tauChainFreshChain)

    obtain A\<^sub>P''' \<Psi>\<^sub>P''' where FrP''': "extractFrame P''' = \<langle>A\<^sub>P''', \<Psi>\<^sub>P'''\<rangle>" and "A\<^sub>P''' \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, P''', xvec)" and "distinct A\<^sub>P'''"
      by(rule freshFrame)
    hence "A\<^sub>P''' \<sharp>* \<Psi>" and "A\<^sub>P''' \<sharp>* A\<^sub>Q" and "A\<^sub>P''' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P''' \<sharp>* M" and "A\<^sub>P''' \<sharp>* R"
      and "A\<^sub>P''' \<sharp>* N" and "A\<^sub>P''' \<sharp>* K" and "A\<^sub>P''' \<sharp>* A\<^sub>R" and "A\<^sub>P''' \<sharp>* P'''" and "A\<^sub>P''' \<sharp>* xvec" and "A\<^sub>P''' \<sharp>* \<Psi>\<^sub>R"
      by simp+

    have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    moreover with QimpP''' FrP''' FrQ \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
    have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'''\<rangle>" using freshCompChain
      by simp
    moreover have "\<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P'''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    ultimately have QImpP''': "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P''', (\<Psi> \<otimes> \<Psi>\<^sub>P''') \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(rule FrameStatEqImpCompose)

    from PChain FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''' \<parallel> R" by(rule tauChainPar1)
    moreover from RTrans FrR P'''Trans MeqK QImpP''' FrP''' FrQ \<open>distinct A\<^sub>P'''\<close> \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>P''' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close>
      \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'''\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* R\<close>
      \<open>A\<^sub>P''' \<sharp>* P'''\<close> \<open>A\<^sub>P''' \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* R\<close>  \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close>
    obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P''' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>R \<sharp>* K'"
      by(rule_tac comm2Aux) (assumption | simp)+
    
    with P'''Trans FrP''' have "\<Psi> \<rhd> P''' \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R')" using FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'''\<close> \<open>A\<^sub>R \<sharp>* R\<close>
      \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>P''' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P''' \<sharp>* P'''\<close> \<open>A\<^sub>P''' \<sharp>* R\<close> \<open>A\<^sub>P''' \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K'\<close> \<open>A\<^sub>P''' \<sharp>* A\<^sub>R\<close>
      by(rule_tac Comm2)
    moreover from P'''Trans \<open>A\<^sub>R \<sharp>* P'''\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>R \<sharp>* P''"
      by(rule_tac outputFreshChainDerivative) auto

    from PChain \<open>A\<^sub>R' \<sharp>* P\<close> have "A\<^sub>R' \<sharp>* P'''" by(rule tauChainFreshChain)
    with P'''Trans \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>R' \<sharp>* P''" using \<open>A\<^sub>R' \<sharp>* xvec\<close>
      by(rule_tac outputFreshChainDerivative) auto
    
    with P''Chain have "A\<^sub>R' \<sharp>* P'" by(rule tauChainFreshChain)
    from \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi> \<otimes> \<Psi>\<^sub>R'"
      by(metis Associativity AssertionStatEqTrans AssertionStatEqSym compositionSym)
    with P''Chain have "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" by(rule tauChainStatEq)
    hence "\<Psi> \<rhd> P'' \<parallel> R' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> R'" using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P''\<close> 
      by(rule tauChainPar1)
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P'' \<parallel> R') \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" 
      using \<open>xvec \<sharp>* \<Psi>\<close> by(rule tauChainResChainPres)
    ultimately have "\<Psi> \<rhd> P \<parallel> R \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" by(drule_tac tauActTauStepChain) auto
    moreover from P'RelQ' \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel"  by(metis C3 Associativity compositionSym)
    with FrR' \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
    with \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'"
      by(rule_tac C2)
    ultimately show ?case by blast
  qed
qed
no_notation relcomp (infixr "O" 75)

lemma weakCongSimBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel'' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PEqQ:   "Eq P Q"
  and     PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     "guarded P"
  and     "guarded Q"
  and     Rel'Rel: "Rel' \<subseteq> Rel"
  and     FrameParPres: "\<And>\<Psi>' \<Psi>\<^sub>U S T U A\<^sub>U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow>
                                            (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel"
  and     C1: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; guarded S; guarded T\<rbrakk> \<Longrightarrow> (\<Psi>', U \<parallel> !S, U \<parallel> !T) \<in> Rel''"
  and     Closed: "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel"
  and     Closed': "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel'"
  and     StatEq: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"
  and     StatEq': "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel'"
  and     Trans: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel"
  and     Trans': "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; (\<Psi>', T, U) \<in> Rel'\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel'"
  and     EqSim: "\<And>\<Psi>' S T. Eq S T \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>\<guillemotleft>Rel\<guillemotright> T"
  and     cSim: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto><Rel> T"
  and     cSym: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     cSym': "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>', T, S) \<in> Rel'"
  and     cExt: "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     cExt': "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel'"
  and     ParPres: "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel"
  and     ParPres': "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel' \<Longrightarrow> (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel'"
  and     ParPres2: "\<And>\<Psi>' S T. Eq S T \<Longrightarrow> Eq (S \<parallel> S) (T \<parallel> T)"
  and     ResPres: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"
  and     ResPres': "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     Assoc: "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"
  and     Assoc': "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel'"
  and     ScopeExt: "\<And>xvec \<Psi>' T S. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel"
  and     ScopeExt': "\<And>xvec \<Psi>' T S. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel'"
  and     Compose: "\<And>\<Psi>' S T U O. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel''; (\<Psi>', U, O) \<in> Rel'\<rbrakk> \<Longrightarrow> (\<Psi>', S, O) \<in> Rel''"
  and     rBangActE: "\<And>\<Psi>' S \<alpha> S'. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<alpha> \<prec> S'; guarded S; bn \<alpha> \<sharp>* S; \<alpha> \<noteq> \<tau>; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow> \<exists>T. \<Psi>' \<rhd> S \<longmapsto>\<alpha> \<prec> T \<and> (\<one>, S', T \<parallel> !S) \<in> Rel'"
  and     rBangTauE: "\<And>\<Psi>' S S'. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<tau> \<prec> S'; guarded S\<rbrakk> \<Longrightarrow> \<exists>T. \<Psi>' \<rhd> S \<parallel> S \<longmapsto>\<tau> \<prec> T \<and> (\<one>, S', T \<parallel> !S) \<in> Rel'"
  and     rBangTauI: "\<And>\<Psi>' S S'. \<lbrakk>\<Psi>' \<rhd> S \<parallel> S \<Longrightarrow>\<^sub>\<tau> S'; guarded S\<rbrakk> \<Longrightarrow> \<exists>T. \<Psi>' \<rhd> !S \<Longrightarrow>\<^sub>\<tau> T \<and> (\<Psi>', T, S' \<parallel> !S) \<in> Rel'"
  shows "\<Psi> \<rhd> R \<parallel> !P \<leadsto>\<guillemotleft>Rel''\<guillemotright> R \<parallel> !Q"
proof(induct rule: weakCongSimI)
  case(cTau RQ')
  from \<open>\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>\<tau> \<prec> RQ'\<close> show ?case
  proof(induct rule: parTauCases[where C="(P, Q, R)"])
    case(cPar1 R' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>extractFrame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = SBottom'" by simp+
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<tau> \<prec> R'\<close> \<open>\<Psi>\<^sub>Q = SBottom'\<close>
    have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> (R' \<parallel> !P)" by(rule_tac Par1) (assumption | simp)+
    hence "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R' \<parallel> !P" by auto
    moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi>, R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel''" using \<open>guarded P\<close> \<open>guarded Q\<close> 
      by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^sub>R \<Psi>\<^sub>R)
    from \<open>A\<^sub>R \<sharp>* (P, Q, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* A\<^sub>R"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R)" in freshFrame) auto
    from FrQ \<open>guarded Q\<close> have "\<Psi>\<^sub>Q \<simeq> \<one>" and "supp \<Psi>\<^sub>Q = ({}::name set)" by(blast dest: guardedStatEq)+
    hence "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>Q" by(auto simp add: fresh_star_def fresh_def)

    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>\<tau> \<prec> Q'\<close> \<open>guarded Q\<close> 
    obtain T where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<parallel> Q \<longmapsto>\<tau> \<prec> T" and "(\<one>, Q', T \<parallel> !Q) \<in> Rel'" 
      by(blast dest: rBangTauE)
    
    from \<open>Eq P Q\<close> have "Eq (P \<parallel> P) (Q \<parallel> Q)" by(rule ParPres2)
    with QTrans 
    obtain S where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> P \<Longrightarrow>\<^sub>\<tau> S" and SRelT: "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
      by(blast dest: EqSim weakCongSimE)
    from PTrans \<open>guarded P\<close> obtain U where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> U" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel'"
      by(blast dest: rBangTauI)
    from PChain \<open>A\<^sub>R \<sharp>* P\<close> have "A\<^sub>R \<sharp>* U" by(force dest: tauStepChainFreshChain)
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> U\<close> FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R \<parallel> U"
      by(rule_tac tauStepChainPar2) auto
    moreover from PTrans \<open>A\<^sub>R \<sharp>* P\<close> have "A\<^sub>R \<sharp>* S" by(force dest: tauStepChainFreshChain)
    from QTrans \<open>A\<^sub>R \<sharp>* Q\<close> have "A\<^sub>R \<sharp>* T" by(force dest: tauFreshChainDerivative)
    have "(\<Psi>, R \<parallel> U, R \<parallel> Q') \<in> Rel''"
    proof -
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel'\<close> Rel'Rel have "(\<Psi> \<otimes> \<Psi>\<^sub>R, U, S \<parallel> !P) \<in> Rel"
        by auto
      hence "(\<Psi>, R \<parallel> U, R \<parallel> (S \<parallel> !P)) \<in> Rel" using FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* U\<close> \<open>A\<^sub>R \<sharp>* S\<close> \<open>A\<^sub>R \<sharp>* P\<close>
        by(rule_tac FrameParPres) auto

      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel\<close> FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* S\<close> \<open>A\<^sub>R \<sharp>* T\<close> have "(\<Psi>, R \<parallel> S, R \<parallel> T) \<in> Rel"
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, R \<parallel> T, R \<parallel> S) \<in> Rel" by(rule cSym)
      hence "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> S) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, (R \<parallel> S) \<parallel> !P, (R \<parallel> T) \<parallel> !P) \<in> Rel" by(rule cSym)
      hence "(\<Psi>, R \<parallel> (S \<parallel> !P), (R \<parallel> T) \<parallel> !P) \<in> Rel" by(metis Trans Assoc)
      ultimately have "(\<Psi>, R \<parallel> U, (R \<parallel> T) \<parallel> !P) \<in> Rel" by(rule Trans)
      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel''" using \<open>guarded P\<close> \<open>guarded Q\<close> by(rule C1)
      moreover from \<open>(\<one>, Q', T \<parallel> !Q) \<in> Rel'\<close> have "(\<one> \<otimes> \<Psi>, Q', T \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', T \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity AssertionStatEqSym Commutativity AssertionStatEqTrans)
      hence "(\<Psi>, R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R \<parallel> T) \<parallel> !Q, R \<parallel> Q') \<in> Rel'" by(rule cSym')
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>Q M N R' A\<^sub>R \<Psi>\<^sub>R K xvec Q' A\<^sub>Q)
    from \<open>A\<^sub>R \<sharp>* (P, Q, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    from \<open>xvec \<sharp>* (P, Q, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have FrQ: "extractFrame(!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'\<close> FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* M\<close>
    obtain A\<^sub>R' \<Psi>\<^sub>R' \<Psi>' where FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>"
      by(rule_tac C="(\<Psi>, xvec, P, Q)" and C'="(\<Psi>, xvec, P, Q)" in expandFrame) auto
    from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'\<close> \<open>guarded Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* K\<close>
    obtain S where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> S" and "(\<one>, Q', S \<parallel> !Q) \<in> Rel'"
      by(fastforce dest: rBangActE)
    ultimately obtain P' T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T" and "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', T, S) \<in> Rel"
      using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>R\<close> \<open>xvec \<sharp>* P\<close>
      by(fastforce dest: cSim weakSimE)

    from PTrans \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* xvec\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
    have "A\<^sub>R \<sharp>* P'" and  "A\<^sub>R' \<sharp>* P'"
      by(force dest: weakOutputFreshChainDerivative)+
    with P'Chain have "A\<^sub>R' \<sharp>* T" by(force dest: tauChainFreshChain)+
    from QTrans \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>A\<^sub>R' \<sharp>* xvec\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> 
    have "A\<^sub>R' \<sharp>* S" by(force dest: outputFreshChainDerivative)

    obtain A\<^sub>Q' \<Psi>\<^sub>Q' where FrQ': "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q' \<sharp>* A\<^sub>R" and "A\<^sub>Q' \<sharp>* M" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R, K, M, R)" in freshFrame) auto
    from FrQ' \<open>guarded Q\<close> have "\<Psi>\<^sub>Q' \<simeq> \<one>" and "supp \<Psi>\<^sub>Q' = ({}::name set)" by(blast dest: guardedStatEq)+
    hence "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>Q'" by(auto simp add: fresh_star_def fresh_def)

    from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                             and NilImpP'': "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                             and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
      using FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R\<close> freshCompChain
      by(drule_tac weakTransitionE) auto

    from PChain have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))"
    proof(induct rule: tauChainCases)
      case TauBase
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'\<close> FrQ have "\<Psi> \<otimes> \<one> \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'" by simp
      moreover note FrR
      moreover from P''Trans \<open>P = P''\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by simp
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule statEqTransition) (metis Identity AssertionStatEqSym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>R\<close> \<open>xvec \<sharp>* P\<close>
        by(force intro: Par1)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using \<open>guarded P\<close> by(rule Bang)
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> FrQ have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" by simp
      ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))" using \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* R\<close>
        by(force intro: Comm1)
      thus ?case by(rule tauActTauStepChain)
    next
      case TauStep
      obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* P"
                          and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "distinct A\<^sub>P''"
        by(rule_tac C="(\<Psi>, K, A\<^sub>R, \<Psi>\<^sub>R, R, P'', P)" in freshFrame) auto
      from PChain \<open>A\<^sub>R \<sharp>* P\<close> have "A\<^sub>R \<sharp>* P''" by(drule_tac tauChainFreshChain) auto
      with FrP'' \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P''" by(drule_tac extractFrameFreshChain) auto
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tauStepChainStatEq) (metis Identity AssertionStatEqSym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" by(rule_tac tauStepChainPar1) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" using \<open>guarded P\<close> by(rule tauStepChainBang)
      hence  "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R \<parallel> (P'' \<parallel> !P)" using FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close>
        by(rule_tac tauStepChainPar2) auto
      moreover have "\<Psi> \<rhd> R \<parallel> (P'' \<parallel> !P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P))"
      proof -
        from FrQ \<open>\<Psi>\<^sub>Q' \<simeq> \<one>\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'"
          by simp (metis statEqTransition AssertionStatEqSym compositionSym)
        moreover from P''Trans have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P'' \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
          by(rule statEqTransition) (metis Identity AssertionStatEqSym)
        hence P''PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<parallel> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (P' \<parallel> !P)" using \<open>xvec \<sharp>* P\<close>
          by(rule_tac Par1) auto
        moreover from FrP'' have FrP''P: "extractFrame(P'' \<parallel> !P) = \<langle>A\<^sub>P'', \<Psi>\<^sub>P'' \<otimes> \<one>\<rangle>"
          by auto
        moreover from FrQ \<open>\<Psi>\<^sub>Q' \<simeq> \<one>\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
          by simp (metis statEqEnt Composition AssertionStatEqSym Commutativity)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M" by(rule chanEqSym)
        moreover have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>)) \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle>"
            by(rule_tac frameResChainPres, simp)
              (metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)
          moreover from NilImpP'' FrQ FrP'' \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R\<close> freshCompChain have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle>"
            by auto
          moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(rule frameResChainPres, simp) 
              (metis Identity AssertionStatEqSym Associativity Commutativity Composition AssertionStatEqTrans)
          ultimately show ?thesis by(rule FrameStatEqImpCompose)
        qed
        ultimately obtain M' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<rhd> R \<longmapsto>M'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'" and "A\<^sub>R \<sharp>* M'"
          using FrR FrQ' \<open>distinct A\<^sub>R\<close> \<open>distinct A\<^sub>P''\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P''\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close>  \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> \<open>A\<^sub>Q' \<sharp>* K\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P'' \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* xvec\<close>
                     \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close>  \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* K\<close> \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close>
          by(rule_tac A\<^sub>Q="A\<^sub>Q'" and Q="Q" in comm2Aux) (assumption | simp)+

        note RTrans FrR P''PTrans FrP''P
        moreover from \<open>\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> M' \<leftrightarrow> K" by(rule chanEqSym)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K" by(metis statEqEnt Composition AssertionStatEqSym Commutativity)
        ultimately show ?thesis using \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P''\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* M'\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close> \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* P\<close> \<open>A\<^sub>P'' \<sharp>* K\<close> \<open>xvec \<sharp>* R\<close>
          by(rule_tac Comm1) (assumption | simp)+
      qed
      ultimately show ?thesis
        by(drule_tac tauActTauStepChain) auto
    qed

    moreover from P'Chain have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>') \<otimes> \<one> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T"
      by(rule tauChainStatEq) (metis Identity AssertionStatEqSym)
    hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> P' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P"
      by(rule_tac tauChainPar1) auto
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>' \<rhd> P' \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P"
      by(rule tauChainStatEq) (metis Associativity)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> P' \<parallel> !P\<Longrightarrow>\<^sup>^\<^sub>\<tau> T \<parallel> !P" using \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close>
      by(rule_tac tauChainStatEq) (auto intro: compositionSym)
    hence "\<Psi> \<rhd> R' \<parallel> (P' \<parallel> !P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> (T \<parallel> !P)" using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* P'\<close>
      by(rule_tac tauChainPar2) auto
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (P' \<parallel> !P)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P))" using \<open>xvec \<sharp>* \<Psi>\<close>
      by(rule tauChainResChainPres)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P))"
      by auto
    moreover have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P)), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel''"
    proof -
      from \<open>((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', T, S) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>', T, S) \<in> Rel"
        by(rule StatEq) (metis Associativity)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R', T, S) \<in> Rel" using \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close>
        by(rule_tac StatEq) (auto dest: compositionSym)

      with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* S\<close> \<open>A\<^sub>R' \<sharp>* T\<close> have "(\<Psi>, R' \<parallel> T, R' \<parallel> S) \<in> Rel"
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, (R' \<parallel> T) \<parallel> !P, (R' \<parallel> S) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> T) \<parallel> !P), \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> S) \<parallel> !P)) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close>
        by(rule ResPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close>
        by(force intro: Trans ScopeExt)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (T \<parallel> !P)), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P) \<in> Rel" using \<open>xvec \<sharp>* \<Psi>\<close>
        by(force intro: Trans ResPres Assoc)

      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !Q) \<in> Rel''"
        by(rule C1)
      moreover from \<open>(\<one>, Q', S \<parallel> !Q) \<in> Rel'\<close> have "(\<one> \<otimes> \<Psi>, Q', S \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', S \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity AssertionStatEqSym Commutativity AssertionStatEqTrans)
      hence "(\<Psi>, R' \<parallel> Q', R' \<parallel> (S \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> S) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R' \<parallel> S) \<parallel> !Q, R' \<parallel> Q') \<in> Rel'" by(rule cSym')
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> S) \<parallel> !Q), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using \<open>xvec \<sharp>* \<Psi>\<close>
        by(rule ResPres')
      hence "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> S)) \<parallel> !Q, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close>
        by(force intro: Trans' ScopeExt'[THEN cSym'])
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>Q M xvec N R' A\<^sub>R \<Psi>\<^sub>R K Q' A\<^sub>Q)
    from \<open>A\<^sub>R \<sharp>* (P, Q, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* R" by simp+
    from \<open>xvec \<sharp>* (P, Q, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* Q" and "xvec \<sharp>* R" by simp+
    have FrQ: "extractFrame(!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> \<open>A\<^sub>R \<sharp>* M\<close>
    obtain p A\<^sub>R' \<Psi>\<^sub>R' \<Psi>' where FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and "distinctPerm p" and "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* R'" and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* xvec" and "A\<^sub>R' \<sharp>* (p \<bullet> xvec)"
      by(rule_tac C="(\<Psi>, P, Q)"  and C'="(\<Psi>, P, Q)" in expandFrame) (assumption | simp)+

    from \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'\<close> S \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* R'\<close>
    have  RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
      by(simp add: boundOutputChainAlpha'' residualInject)
    from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" by(rule cExt)
    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'\<close> S \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>xvec \<sharp>* Q\<close> \<open>distinctPerm p\<close>
    have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" by(rule_tac inputAlpha) auto
    then obtain S where QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> S" and "(\<one>, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel'" 
      using \<open>guarded Q\<close>
      by(fastforce dest: rBangActE)
    ultimately obtain P' T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R : Q \<rhd> P \<Longrightarrow>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" 
                             and P'Chain: "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>') \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> T" 
                             and "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'), T, S) \<in> Rel"
      by(fastforce dest: cSim weakSimE)

    from \<open>A\<^sub>R' \<sharp>* N\<close> \<open>A\<^sub>R' \<sharp>* xvec\<close> \<open>A\<^sub>R' \<sharp>* (p \<bullet> xvec)\<close> S have "A\<^sub>R' \<sharp>* (p \<bullet> N)"
      by(simp add: freshChainSimps)
    with PTrans \<open>A\<^sub>R' \<sharp>* P\<close> have "A\<^sub>R' \<sharp>* P'" by(force dest: weakInputFreshChainDerivative)
    with P'Chain have "A\<^sub>R' \<sharp>* T" by(force dest: tauChainFreshChain)+
    from QTrans \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>A\<^sub>R' \<sharp>* (p \<bullet> N)\<close> have "A\<^sub>R' \<sharp>* S" by(force dest: inputFreshChainDerivative)

    obtain A\<^sub>Q' \<Psi>\<^sub>Q' where FrQ': "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q'\<rangle>" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q' \<sharp>* A\<^sub>R" and "A\<^sub>Q' \<sharp>* M" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K"
      by(rule_tac C="(\<Psi>, \<Psi>\<^sub>R, A\<^sub>R, K, M, R)" in freshFrame) auto
    from FrQ' \<open>guarded Q\<close> have "\<Psi>\<^sub>Q' \<simeq> \<one>" and "supp \<Psi>\<^sub>Q' = ({}::name set)" by(blast dest: guardedStatEq)+
    hence "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>Q'" by(auto simp add: fresh_star_def fresh_def)

    from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                             and NilImpP'': "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>R)"
                             and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'"
      using FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R\<close> freshCompChain
      by(drule_tac weakTransitionE) auto

    from \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> PChain have "(p \<bullet> xvec) \<sharp>* P''" and "xvec \<sharp>* P''" 
      by(force dest: tauChainFreshChain)+
    from \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>distinctPerm p\<close> have "xvec \<sharp>* (p \<bullet> N)"
      by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, where pi=p, symmetric]) simp
    with P''Trans \<open>xvec \<sharp>* P''\<close> have "xvec \<sharp>* P'" by(force dest: inputFreshChainDerivative)
    hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])

    from PChain have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))"
    proof(induct rule: tauChainCases)
      case TauBase
      from RTrans FrQ have "\<Psi> \<otimes> \<one> \<rhd> R \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')" by simp
      moreover note FrR
      moreover from P''Trans \<open>P = P''\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr>\<prec> P'" by simp
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" 
        by(rule statEqTransition) (metis Identity AssertionStatEqSym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)" by(force intro: Par1)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)" using \<open>guarded P\<close> by(rule Bang)
      moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> FrQ have "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<one> \<turnstile> M \<leftrightarrow> K" by simp
      ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))" using \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
        by(force intro: Comm2)
      thus ?case by(rule tauActTauStepChain)
    next
      case TauStep
      obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* P"
                          and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "distinct A\<^sub>P''"
        by(rule_tac C="(\<Psi>, K, A\<^sub>R, \<Psi>\<^sub>R, R, P'', P)" in freshFrame) auto
      from PChain \<open>A\<^sub>R \<sharp>* P\<close> have "A\<^sub>R \<sharp>* P''" by(drule_tac tauChainFreshChain) auto
      with FrP'' \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> have "A\<^sub>R \<sharp>* \<Psi>\<^sub>P''" by(drule_tac extractFrameFreshChain) auto
      from \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(rule tauStepChainStatEq) (metis Identity AssertionStatEqSym)
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" by(rule_tac tauStepChainPar1) auto
      hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> !P" using \<open>guarded P\<close> by(rule tauStepChainBang)
      hence  "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> R \<parallel> (P'' \<parallel> !P)" using FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close>
        by(rule_tac tauStepChainPar2) auto
      moreover have "\<Psi> \<rhd> R \<parallel> (P'' \<parallel> !P) \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> (P' \<parallel> !P))"
      proof -
        from FrQ \<open>\<Psi>\<^sub>Q' \<simeq> \<one>\<close> RTrans have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<rhd> R \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
          by simp (metis statEqTransition AssertionStatEqSym compositionSym)
        moreover from P''Trans have "(\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<one> \<rhd> P'' \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'"
          by(rule statEqTransition) (metis Identity AssertionStatEqSym)
        hence P''PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P'' \<parallel> !P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (P' \<parallel> !P)"
          by(rule_tac Par1) auto
        moreover from FrP'' have FrP''P: "extractFrame(P'' \<parallel> !P) = \<langle>A\<^sub>P'', \<Psi>\<^sub>P'' \<otimes> \<one>\<rangle>"
          by auto
        moreover from FrQ \<open>\<Psi>\<^sub>Q' \<simeq> \<one>\<close> \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K"
          by simp (metis statEqEnt Composition AssertionStatEqSym Commutativity)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>Q' \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M" by(rule chanEqSym)
        moreover have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>)) \<otimes> \<Psi>\<^sub>R\<rangle>"
        proof -
          have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>Q') \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle>"
            by(rule_tac frameResChainPres, simp)
              (metis Associativity Commutativity Composition AssertionStatEqTrans AssertionStatEqSym)
          moreover from NilImpP'' FrQ FrP'' \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R\<close> freshCompChain have "\<langle>A\<^sub>Q', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle>"
            by auto
          moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R\<rangle>"
            by(rule frameResChainPres, simp) 
              (metis Identity AssertionStatEqSym Associativity Commutativity Composition AssertionStatEqTrans)
          ultimately show ?thesis by(rule FrameStatEqImpCompose)
        qed
        ultimately obtain M' where RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<rhd> R \<longmapsto>M'\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')" and "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'" and "A\<^sub>R \<sharp>* M'"
          using FrR FrQ' \<open>distinct A\<^sub>R\<close> \<open>distinct A\<^sub>P''\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P''\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close>  \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> \<open>A\<^sub>Q' \<sharp>* K\<close> \<open>A\<^sub>Q' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P'' \<sharp>* P\<close>
                     \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close>  \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* K\<close>
          by(rule_tac A\<^sub>Q="A\<^sub>Q'" and Q="Q" in comm1Aux) (assumption | simp)+

        note RTrans FrR P''PTrans FrP''P
        moreover from \<open>\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> K \<leftrightarrow> M'\<close> have "\<Psi> \<otimes> (\<Psi>\<^sub>P'' \<otimes> \<one>) \<otimes> \<Psi>\<^sub>R \<turnstile> M' \<leftrightarrow> K" by(rule chanEqSym)
        hence "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>P'' \<otimes> \<one> \<turnstile> M' \<leftrightarrow> K" by(metis statEqEnt Composition AssertionStatEqSym Commutativity)
        ultimately show ?thesis using \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P''\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* M'\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close> \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* P\<close> \<open>A\<^sub>P'' \<sharp>* K\<close> \<open>(p \<bullet> xvec) \<sharp>* P''\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close>
          by(rule_tac Comm2) (assumption | simp)+
      qed
      ultimately show ?thesis
        by(drule_tac tauActTauStepChain) auto
    qed
    hence "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> P') \<parallel> !P))" 
      using \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* (p \<bullet> P')\<close> \<open>(p \<bullet> xvec) \<sharp>* R'\<close> S \<open>distinctPerm p\<close>
      by(subst resChainAlpha[where p=p]) auto
    moreover from P'Chain have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'))) \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)"
      by(rule tauChainEqvt)
    with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S \<open>distinctPerm p\<close>
    have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)" by(simp add: eqvts)
    hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>') \<otimes> \<one> \<rhd> (p \<bullet> P') \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T)"
      by(rule tauChainStatEq) (metis Identity AssertionStatEqSym)
    hence "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P"
      by(rule_tac tauChainPar1) auto
    hence "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P"
      by(rule tauChainStatEq) (metis Associativity)
    hence "\<Psi> \<otimes> \<Psi>\<^sub>R' \<rhd> (p \<bullet> P') \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> T) \<parallel> !P" using \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq>  \<Psi>\<^sub>R'\<close>
      by(rule_tac tauChainStatEq) (auto intro: compositionSym)
    hence "\<Psi> \<rhd> R' \<parallel> ((p \<bullet> P') \<parallel> !P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> R' \<parallel> ((p \<bullet> T) \<parallel> !P)" 
      using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* xvec\<close> \<open>A\<^sub>R' \<sharp>* (p \<bullet> xvec)\<close> S
      by(rule_tac tauChainPar2) (auto simp add: freshChainSimps)
    hence "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> P') \<parallel> !P)) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P))" using \<open>xvec \<sharp>* \<Psi>\<close>
      by(rule tauChainResChainPres)
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P))"
      by auto
    moreover have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P)), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel''"
    proof -
      from \<open>((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>'), T, S) \<in> Rel\<close> 
      have "(p \<bullet> ((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> (p \<bullet> \<Psi>')), (p \<bullet> T), (p \<bullet> S)) \<in> Rel"
        by(rule Closed)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>distinctPerm p\<close> S
      have "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', p \<bullet> T, p \<bullet> S) \<in> Rel"
        by(simp add: eqvts)
      hence "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>', p \<bullet> T, p \<bullet> S) \<in> Rel"
        by(rule StatEq) (metis Associativity)
      hence "(\<Psi> \<otimes> \<Psi>\<^sub>R', p \<bullet> T, p \<bullet> S) \<in> Rel" using \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close>
        by(rule_tac StatEq) (auto dest: compositionSym)
      moreover from \<open>A\<^sub>R' \<sharp>* S\<close> \<open>A\<^sub>R' \<sharp>* T\<close> \<open>A\<^sub>R' \<sharp>* xvec\<close> \<open>A\<^sub>R' \<sharp>* (p \<bullet> xvec)\<close> S
      have "A\<^sub>R' \<sharp>* (p \<bullet> S)" and "A\<^sub>R' \<sharp>* (p \<bullet> T)"
        by(simp add: freshChainSimps)+
      ultimately have "(\<Psi>, R' \<parallel> (p \<bullet> T), R' \<parallel> (p \<bullet> S)) \<in> Rel" using FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close>
        by(rule_tac FrameParPres) auto
      hence "(\<Psi>, (R' \<parallel> (p \<bullet> T)) \<parallel> !P, (R' \<parallel> (p \<bullet> S)) \<parallel> !P) \<in> Rel" by(rule ParPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> T)) \<parallel> !P), \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> S)) \<parallel> !P)) \<in> Rel" 
        using \<open>xvec \<sharp>* \<Psi>\<close>
        by(rule ResPres)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P) \<in> Rel" 
        using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close>
        by(force intro: Trans ScopeExt)
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> ((p \<bullet> T) \<parallel> !P)), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P) \<in> Rel"
        using \<open>xvec \<sharp>* \<Psi>\<close>
        by(force intro: Trans ResPres Assoc)
      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> 
      have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !Q) \<in> Rel''"
        by(rule C1)
      moreover from \<open>(\<one>, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel'\<close> 
      have "(p \<bullet> \<one>, p \<bullet> p \<bullet> Q', p \<bullet> (S \<parallel> !Q)) \<in> Rel'" by(rule Closed')
      with \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> S \<open>distinctPerm p\<close> 
        have "(\<one>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" by(simp add: eqvts)
      hence "(\<one> \<otimes> \<Psi>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" by(rule cExt')
      hence "(\<Psi>, Q', (p \<bullet> S) \<parallel> !Q) \<in> Rel'" 
        by(rule StatEq') (metis Identity AssertionStatEqSym Commutativity AssertionStatEqTrans)
      hence "(\<Psi>, R' \<parallel> Q', R' \<parallel> ((p \<bullet> S) \<parallel> !Q)) \<in> Rel'" by(rule ParPres')
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> (p \<bullet> S)) \<parallel> !Q) \<in> Rel'" by(metis Trans' Assoc')
      hence "(\<Psi>, (R' \<parallel> (p \<bullet> S)) \<parallel> !Q, R' \<parallel> Q') \<in> Rel'" by(rule cSym')
      hence "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>((R' \<parallel> (p \<bullet> S)) \<parallel> !Q), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using \<open>xvec \<sharp>* \<Psi>\<close>
        by(rule ResPres')
      hence "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> S))) \<parallel> !Q, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* Q\<close>
        by(force intro: Trans' ScopeExt'[THEN cSym'])
      ultimately show ?thesis by(rule_tac Compose)
    qed
    ultimately show ?case by blast
  qed
qed
notation relcomp (infixr "O" 75)

end

end
