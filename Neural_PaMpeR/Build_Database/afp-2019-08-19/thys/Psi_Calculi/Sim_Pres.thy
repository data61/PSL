(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Sim_Pres
  imports Simulation
begin

context env begin

lemma inputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes PRelQ: "\<And>Tvec. length xvec = length Tvec \<Longrightarrow> (\<Psi>, P[xvec::=Tvec], Q[xvec::=Tvec]) \<in> Rel"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<leadsto>[Rel] M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.Q \<longmapsto>\<alpha> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: inputCases) (auto intro: Input PRelQ)
qed

lemma outputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<leadsto>[Rel] M\<langle>N\<rangle>.Q"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> M\<langle>N\<rangle>.Q \<longmapsto>\<alpha> \<prec> Q'"
  thus "\<exists>P'. \<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel"
    by(induct rule: outputCases) (auto intro: Output PRelQ)
qed

lemma casePres:
  fixes \<Psi>    :: 'b
  and   CsP  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   CsQ  :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   M    :: 'a
  and   N    :: 'a

  assumes PRelQ: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<Psi>, P, Q) \<in> Rel"
  and     Sim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[Rel] S"
  and          "Rel \<subseteq> Rel'"

  shows "\<Psi> \<rhd> Cases CsP \<leadsto>[Rel'] Cases CsQ"
proof(auto simp add: simulation_def residual.inject psi.inject)
  fix \<alpha> Q'
  assume "\<Psi> \<rhd> Cases CsQ \<longmapsto>\<alpha> \<prec> Q'" and "bn \<alpha> \<sharp>* CsP" and "bn \<alpha> \<sharp>* \<Psi>"
  thus "\<exists>P'. \<Psi> \<rhd> Cases CsP \<longmapsto>\<alpha> \<prec> P' \<and> (\<Psi>, P', Q') \<in> Rel'"
  proof(induct rule: caseCases)
    case(cCase \<phi> Q)
    from \<open>(\<phi>, Q) mem CsQ\<close> obtain P where "(\<phi>, P) mem CsP" and "guarded P" and "(\<Psi>, P, Q) \<in> Rel"
      by(metis PRelQ)
    from \<open>(\<Psi>, P, Q) \<in> Rel\<close> have "\<Psi> \<rhd> P \<leadsto>[Rel] Q" by(rule Sim)
    moreover from \<open>bn \<alpha> \<sharp>* CsP\<close> \<open>(\<phi>, P) mem CsP\<close> have "bn \<alpha> \<sharp>* P" by(auto dest: memFreshChain)
    moreover note \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>
    ultimately obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> have "\<Psi> \<rhd> Cases CsP \<longmapsto>\<alpha> \<prec> P'"
      by(rule Case)
    moreover from P'RelQ' \<open>Rel \<subseteq> Rel'\<close> have "(\<Psi>, P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed

lemma resPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   x    :: name
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel'"
  and     "x \<sharp> \<Psi>"
  and     "Rel \<subseteq> Rel'"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<leadsto>[Rel'] \<lparr>\<nu>x\<rparr>Q"
proof -
  note \<open>eqvt Rel'\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "x \<sharp> \<lparr>\<nu>x\<rparr>P" and "x \<sharp> \<lparr>\<nu>x\<rparr>Q" by(simp add: abs_fresh)+
  ultimately show ?thesis
  proof(induct rule: simIFresh[where C="()"])
    case(cSim \<alpha> Q') 
    from \<open>bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>P\<close> \<open>bn \<alpha> \<sharp>* \<lparr>\<nu>x\<rparr>Q\<close> \<open>x \<sharp> \<alpha>\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" by simp+
    from \<open>\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> \<open>x \<sharp> Q'\<close>  \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> 
         \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>x \<sharp> \<alpha>\<close>
    show ?case
    proof(induct rule: resCases)
      case(cOpen M xvec1 xvec2 y N Q')
      from \<open>bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* \<Psi>\<close> have "xvec1 \<sharp>* \<Psi>" and "y \<sharp> \<Psi>" and "xvec2 \<sharp>* \<Psi>" by simp+
      from \<open>bn (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>) \<sharp>* P\<close> have "xvec1 \<sharp>* P" and "y \<sharp> P" and "xvec2 \<sharp>* P" by simp+
      from \<open>x \<sharp> (M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle>)\<close> have "x \<sharp> xvec1" and "x \<noteq> y" and "x \<sharp> xvec2" and "x \<sharp> M" by simp+
      from PSimQ \<open>\<Psi> \<rhd> Q \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> ([(x, y)] \<bullet> Q')\<close> 
           \<open>xvec1 \<sharp>* \<Psi>\<close> \<open>xvec2 \<sharp>* \<Psi>\<close> \<open>xvec1 \<sharp>* P\<close> \<open>xvec2 \<sharp>* P\<close>
      obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec1@xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'" and P'RelQ': "(\<Psi>, P', ([(x, y)] \<bullet> Q')) \<in> Rel"
        by(force dest: simE)
      from \<open>y \<in> supp N\<close> \<open>x \<noteq> y\<close> have "x \<in> supp([(x, y)] \<bullet> N)" 
        by(drule_tac pt_set_bij2[OF pt_name_inst, OF at_name_inst, where pi="[(x, y)]"]) (simp add: eqvts calc_atm)
      with PTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'"
        by(rule_tac Open)
      hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> \<lparr>\<nu>x\<rparr>P) \<longmapsto>([(x, y)] \<bullet> (M\<lparr>\<nu>*(xvec1@x#xvec2)\<rparr>\<langle>([(x, y)] \<bullet> N)\<rangle> \<prec> P'))"
        by(rule eqvts)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> \<open>y \<sharp> P\<close> \<open>x \<sharp> M\<close> \<open>y \<sharp> M\<close> \<open>x \<sharp> xvec1\<close> \<open>y \<sharp> xvec1\<close> \<open>x \<sharp> xvec2\<close> \<open>y \<sharp> xvec2\<close> \<open>x \<noteq> y\<close>
      have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>M\<lparr>\<nu>*(xvec1@y#xvec2)\<rparr>\<langle>N\<rangle> \<prec> ([(x, y)] \<bullet> P')" by(simp add: eqvts calc_atm alphaRes)
      moreover from P'RelQ' \<open>Rel \<subseteq> Rel'\<close> \<open>eqvt Rel'\<close> have "([(y, x)] \<bullet> \<Psi>, [(y, x)] \<bullet> P', [(y, x)] \<bullet> [(x, y)] \<bullet> Q') \<in> Rel'"
        by(force simp add: eqvt_def)
      with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "(\<Psi>, [(x, y)] \<bullet> P', Q') \<in> Rel'" by(simp add: name_swap)
      ultimately show ?case by blast
    next
      case(cRes Q')
      from PSimQ \<open>\<Psi> \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* P\<close>
      obtain P' where PTrans: "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
        by(rule Scope)
      moreover from P'RelQ' \<open>x \<sharp> \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>x\<rparr>P', \<lparr>\<nu>x\<rparr>Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    qed
  qed
qed

lemma resChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "eqvt Rel"
  and     "xvec \<sharp>* \<Psi>"
  and     C1:    "\<And>\<Psi>' R S y. \<lbrakk>(\<Psi>', R, S) \<in> Rel; y \<sharp> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel"

  shows   "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q"
using \<open>xvec \<sharp>* \<Psi>\<close>
proof(induct xvec)
  case Nil
  from PSimQ show ?case by simp
next
  case(Cons x xvec)
  from \<open>(x#xvec) \<sharp>* \<Psi>\<close> have "x \<sharp> \<Psi>" and "xvec \<sharp>* \<Psi>" by simp+
  from \<open>xvec \<sharp>* \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<leadsto>[Rel] \<lparr>\<nu>*xvec\<rparr>Q" by(rule Cons)
  moreover note \<open>eqvt Rel\<close> \<open>x \<sharp> \<Psi>\<close>
  moreover have "Rel \<subseteq> Rel" by simp
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>Q)" using C1
    by(rule resPres)
  thus ?case by simp
qed

lemma parPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  
  assumes PRelQ: "\<And>A\<^sub>R \<Psi>\<^sub>R. \<lbrakk>extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> (\<Psi> \<otimes> \<Psi>\<^sub>R, P, Q) \<in> Rel" 
  and     Eqvt: "eqvt Rel"
  and     Eqvt': "eqvt Rel'"

  and     StatImp: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> insertAssertion (extractFrame T) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (extractFrame S) \<Psi>'"
  and     Sim:     "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     Ext: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"


  and     C1: "\<And>\<Psi>' S T A\<^sub>U \<Psi>\<^sub>U U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     C2: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel'; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel'"
  and     C3: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"

  shows "\<Psi> \<rhd> P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
using Eqvt'
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> QR)
  from \<open>bn \<alpha> \<sharp>* (P \<parallel> R)\<close> \<open>bn \<alpha> \<sharp>* (Q \<parallel> R)\<close>
  have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R"
    by simp+
  from \<open>\<Psi> \<rhd> Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
  show ?case
  proof(induct rule: parCases[where C = "(P, R)"])
    case(cPar1 Q' A\<^sub>R \<Psi>\<^sub>R)
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P" by simp
    have FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>A\<^sub>R \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* R\<close> FrR
    have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(drule_tac extractFrameFreshChain) auto
    from FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto>[Rel] Q"
      by(blast intro: Sim PRelQ)
    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    ultimately obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
                           and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
    using \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<^sub>R\<close> \<open>bn \<alpha> \<sharp>* P\<close>
      by(force dest: simE)
    from PTrans QTrans \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
      by(blast dest: freeFreshChainDerivative)+
    from PTrans \<open>bn \<alpha> \<sharp>* R\<close> FrR  \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<alpha> \<prec> (P' \<parallel> R)" 
      by(rule_tac Par1) 
    moreover from P'RelQ' FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>R \<sharp>* Q'\<close> have "(\<Psi>, P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 R' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, \<alpha>, R)"
      by(rule freshFrame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* \<alpha>" and "A\<^sub>P \<sharp>* R"
      by simp+

    have FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* P\<close> FrP \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P"
      by(drule_tac extractFrameFreshChain) auto

    from FrP FrQ \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
    have "bn \<alpha> \<sharp>* \<Psi>\<^sub>P" and "bn \<alpha> \<sharp>* \<Psi>\<^sub>Q"
      by(force dest: extractFrameFreshChain)+


    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* (\<Psi>, P, Q, A\<^sub>Q, A\<^sub>P, \<Psi>\<^sub>Q, \<Psi>\<^sub>P, \<alpha>, R)" and "distinct A\<^sub>R"
      by(rule freshFrame)
    then have "A\<^sub>R \<sharp>* \<Psi>" and "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* Q" and "A\<^sub>R \<sharp>* A\<^sub>Q" and  "A\<^sub>R \<sharp>* A\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<alpha>" and "A\<^sub>R \<sharp>* R"
      by simp+

    from \<open>A\<^sub>Q \<sharp>* R\<close>  FrR \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extractFrameFreshChain) auto
    from \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> FrR  have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R"
      by(drule_tac extractFrameFreshChain) auto

    have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'" by fact
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>"
        by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym FrameStatEqSym)
      moreover from FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
      have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> \<Psi>\<^sub>R))"
        by(blast intro: PRelQ StatImp)
      with FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>" using freshCompChain by auto
      moreover have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(metis frameIntAssociativity Commutativity FrameStatEqTrans frameIntCompositionSym frameIntAssociativity[THEN FrameStatEqSym])
      ultimately show ?thesis
        by(rule FrameStatEqImpCompose)
    qed

    ultimately have "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>\<alpha> \<prec> R'"
      using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
            \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> FrR \<open>distinct A\<^sub>R\<close>
      by(force intro: transferFrame)
    with \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close>  \<open>A\<^sub>P \<sharp>* R\<close>  \<open>A\<^sub>P \<sharp>* \<alpha>\<close> FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<alpha> \<prec> (P \<parallel> R')"
      by(force intro: Par2)
    moreover obtain A\<^sub>R' \<Psi>\<^sub>R' where "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac freshFrame[where C="(\<Psi>, P, Q)"]) auto

    moreover from RTrans FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha>  \<sharp>* P\<close> \<open>bn \<alpha>  \<sharp>* Q\<close> \<open>bn \<alpha>  \<sharp>* R\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
    obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set(bn \<alpha>) \<times> set(bn(p \<bullet> \<alpha>))" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                           and "bn(p \<bullet> \<alpha>) \<sharp>* R" and "bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>" and "bn(p \<bullet> \<alpha>) \<sharp>* P" and "bn(p \<bullet> \<alpha>) \<sharp>* Q" and "bn(p \<bullet> \<alpha>) \<sharp>* R"
                           and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, Q, R)" and C'="(\<Psi>, P, Q, R)" in expandFrame) (assumption | simp)+

    from \<open>A\<^sub>R \<sharp>* \<Psi>\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> \<Psi>)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* \<Psi>\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>" by simp
    from \<open>A\<^sub>R \<sharp>* P\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> P)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>bn \<alpha> \<sharp>* P\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* P\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* P" by simp
    from \<open>A\<^sub>R \<sharp>* Q\<close> have "(p \<bullet> A\<^sub>R) \<sharp>* (p \<bullet> Q)" by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])
    with \<open>bn \<alpha> \<sharp>* Q\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* Q\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* Q" by simp

    from FrR have "(p \<bullet> extractFrame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
    with \<open>bn \<alpha> \<sharp>* R\<close> \<open>bn(p \<bullet> \<alpha>) \<sharp>* R\<close> S have "extractFrame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(simp add: eqvts)

    with \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), P, Q) \<in> Rel" by(rule_tac PRelQ)

    hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P, Q) \<in> Rel" by(rule Ext)
    with \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P, Q) \<in> Rel" by(blast intro: C3 Associativity compositionSym)
    with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> have "(\<Psi>, P \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule_tac C1) 
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>R M N Q' A\<^sub>Q \<Psi>\<^sub>Q K xvec R' A\<^sub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+

    have  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+

    from \<open>xvec \<sharp>* (P, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+
  
    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, M, N, K, R, P, xvec)" and "distinct A\<^sub>P"
      by(rule freshFrame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* R"
      and "A\<^sub>P \<sharp>* N" and "A\<^sub>P \<sharp>* K" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* xvec"
      by simp+

    have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>N\<rparr> \<prec> Q'" and RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'"
      and MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow>K" by fact+

    from FrP FrR \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>xvec \<sharp>* P\<close>
    have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P"
      by(fastforce dest!: extractFrameFreshChain)+
  
  from RTrans FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* Q\<close> \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
                  \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* xvec\<close>
                  \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>P\<close> \<open>distinct xvec\<close> \<open>xvec \<sharp>* M\<close>
  obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>"
                         and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* Q" and "A\<^sub>R' \<sharp>* \<Psi>" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                         and "(p \<bullet> xvec) \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* K" and "(p \<bullet> xvec) \<sharp>* R"
                         and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>P" and "(p \<bullet> xvec) \<sharp>* A\<^sub>Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>P"
                         and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* N"
    by(rule_tac C="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P)" and C'="(\<Psi>, Q, \<Psi>\<^sub>Q, K, R, P, A\<^sub>P, A\<^sub>Q, \<Psi>\<^sub>P)" in expandFrame) 
      (assumption | simp)+

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
  
  from \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* M\<close> S have "A\<^sub>P \<sharp>* (p \<bullet> M)" by(simp add: freshChainSimps)
  from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* M\<close> S have "A\<^sub>Q \<sharp>* (p \<bullet> M)" by(simp add: freshChainSimps)
  from \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P" by(simp add: freshChainSimps)
  from \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> S have "(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q" by(simp add: freshChainSimps)
  
  from QTrans S \<open>xvec \<sharp>* Q\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(rule_tac inputPermFrameSubject) (assumption | auto simp add: fresh_star_def)+
  with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> S have QTrans: "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<rhd> Q \<longmapsto> (p \<bullet> M)\<lparr>N\<rparr> \<prec> Q'"
    by(simp add: eqvts)

  from FrR have "(p \<bullet> extractFrame R) = p \<bullet> \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by simp
  with \<open>xvec \<sharp>* R\<close> \<open>(p \<bullet> xvec) \<sharp>* R\<close> S have FrR: "extractFrame R = \<langle>(p \<bullet> A\<^sub>R), (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
    by(simp add: eqvts)

  note RTrans FrR
  moreover from FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> have "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<leadsto>[Rel] Q"
    by(metis Sim PRelQ)
  with QTrans obtain P' where PTrans: "\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<rhd> P \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'" and P'RelQ': "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), P', Q') \<in> Rel"
    by(force dest: simE)
  from PTrans QTrans \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>A\<^sub>R' \<sharp>* N\<close> have "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
    by(blast dest: inputFreshChainDerivative)+
    
  note PTrans
  moreover from MeqK have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R)) \<turnstile> (p \<bullet> M) \<leftrightarrow> (p \<bullet> K)" by(rule chanEqClosed)
  with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>Q\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<^sub>Q\<close> \<open>xvec \<sharp>* K\<close> \<open>(p \<bullet> xvec) \<sharp>* K\<close> S
  have MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K" by(simp add: eqvts)
  
  moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
  proof -
    have "\<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle>"
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    moreover from FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close>
    have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R))) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)))"
      by(metis PRelQ StatImp)
    with FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q \<sharp>* xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>Q\<close> S
    have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>P\<rangle>" using freshCompChain
      by(simp add: freshChainSimps)
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> (p \<bullet> \<Psi>\<^sub>R)\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
      by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
    ultimately show ?thesis by(rule_tac FrameStatEqImpCompose)
  qed
  moreover note FrP FrQ \<open>distinct A\<^sub>P\<close>
  moreover from \<open>distinct A\<^sub>R\<close> have "distinct(p \<bullet> A\<^sub>R)" by simp
  moreover note \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close>  \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* Q\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K\<close>
                \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* (p \<bullet> M)\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* (p \<bullet> M)\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* R\<close>
  ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> (p \<bullet> \<Psi>\<^sub>R) \<turnstile> (p \<bullet> M) \<leftrightarrow> K'" and "(p \<bullet> A\<^sub>R) \<sharp>* K'"
    by(rule_tac comm1Aux)

  with PTrans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR \<open>(p \<bullet> A\<^sub>R) \<sharp>* \<Psi>\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* P\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* R\<close>
    \<open>xvec \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* (p \<bullet> M)\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* K'\<close> \<open>(p \<bullet> A\<^sub>R) \<sharp>* A\<^sub>P\<close>
    by(rule_tac Comm1) (assumption | simp)+

  moreover from P'RelQ' have  "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
  with \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel" by(metis C3 Associativity compositionSym)
  with FrR' \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule_tac C1)
  with \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
  ultimately show ?case by blast
next
    case(cComm2 \<Psi>\<^sub>R M xvec N Q' A\<^sub>Q \<Psi>\<^sub>Q K R' A\<^sub>R)
    have  FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" by fact
    from \<open>A\<^sub>Q \<sharp>* (P, R)\<close> have "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* R" by simp+

    have  FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact
    from \<open>A\<^sub>R \<sharp>* (P, R)\<close> have "A\<^sub>R \<sharp>* P" and "A\<^sub>R \<sharp>* R" by simp+

    from \<open>xvec \<sharp>* (P, R)\<close> have "xvec \<sharp>* P" and "xvec \<sharp>* R" by simp+

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* (\<Psi>, A\<^sub>Q, \<Psi>\<^sub>Q, A\<^sub>R, M, N, K, R, P, xvec)" and "distinct A\<^sub>P"
      by(rule freshFrame)
    hence "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* A\<^sub>Q" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P \<sharp>* M" and "A\<^sub>P \<sharp>* R"
      and "A\<^sub>P \<sharp>* N" "A\<^sub>P \<sharp>* K" and "A\<^sub>P \<sharp>* A\<^sub>R" and "A\<^sub>P \<sharp>* P"  and "A\<^sub>P \<sharp>* xvec" 
      by simp+

    from FrP FrR \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* xvec\<close> \<open>xvec \<sharp>* P\<close>
    have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P" and  "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "xvec \<sharp>* \<Psi>\<^sub>P"
      by(fastforce dest!: extractFrameFreshChain)+

    have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact 

    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>K\<lparr>N\<rparr> \<prec> R'\<close> FrR \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close>
    moreover from FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<leadsto>[Rel] Q" by(metis PRelQ Sim)
    with QTrans obtain P' where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and P'RelQ': "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', Q') \<in> Rel"
      using \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* \<Psi>\<^sub>R\<close> \<open>xvec \<sharp>* P\<close>
      by(force dest: simE)
    from PTrans QTrans \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close> have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
      by(blast dest: outputFreshChainDerivative)+
    note PTrans \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K\<close>
    moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
    proof -
      have "\<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
        by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
      moreover from FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close>
      have "(insertAssertion (extractFrame Q) (\<Psi> \<otimes> \<Psi>\<^sub>R)) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P) (\<Psi> \<otimes> \<Psi>\<^sub>R))"
        by(metis PRelQ StatImp)
      with FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close>
      have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>P\<rangle>" using freshCompChain by simp
      moreover have "\<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle>" 
        by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
      ultimately show ?thesis by(rule_tac FrameStatEqImpCompose)
    qed
    moreover note FrP FrQ \<open>distinct A\<^sub>P\<close> \<open>distinct A\<^sub>R\<close>
    moreover from \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>Q \<sharp>* A\<^sub>R\<close> have "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* A\<^sub>Q" by simp+
    moreover note \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* K\<close>  \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
                  \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>xvec \<sharp>* M\<close>
    ultimately obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'" and "\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>R \<sharp>* K'"
      by(rule_tac comm2Aux) assumption+

    with PTrans FrP have "\<Psi> \<rhd> P \<parallel> R \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R')" using FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* R\<close>
      \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* R\<close> and \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>R\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* K'\<close>
      by(force intro: Comm2)

    moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> R \<longmapsto>K'\<lparr>N\<rparr> \<prec> R'\<close> FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>R \<sharp>* Q'\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* K'\<close>
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where  ReqR': "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" 
                         and "A\<^sub>R' \<sharp>* \<Psi>" and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
      by(rule_tac C="(\<Psi>, P', Q')" and C'="\<Psi>" in expandFrame) auto

    from P'RelQ' have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', Q') \<in> Rel" by(rule Ext)
    with ReqR' have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', Q') \<in> Rel" by(metis C3 Associativity compositionSym)
    with FrR' \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> have "(\<Psi>, P' \<parallel> R', Q' \<parallel> R') \<in> Rel'"
      by(rule_tac C1)
    with \<open>xvec \<sharp>* \<Psi>\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> R'), \<lparr>\<nu>*xvec\<rparr>(Q' \<parallel> R')) \<in> Rel'" by(rule_tac C2)
    ultimately show ?case by blast
  qed
qed
no_notation relcomp (infixr "O" 75)
lemma bangPres:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"
  and   Rel  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Rel' :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> Rel"
  and     "eqvt Rel'"
  and     "guarded P"
  and     "guarded Q"
  and     cSim: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> \<Psi>' \<rhd> S \<leadsto>[Rel] T"
  and     cExt: "\<And>\<Psi>' S T \<Psi>''. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', S, T) \<in> Rel"
  and     cSym: "\<And>\<Psi>' S T. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', T, S) \<in> Rel"
  and     StatEq: "\<And>\<Psi>' S T \<Psi>''. \<lbrakk>(\<Psi>', S, T) \<in> Rel; \<Psi>' \<simeq> \<Psi>''\<rbrakk> \<Longrightarrow> (\<Psi>'', S, T) \<in> Rel"
  and     Closed: "\<And>\<Psi>' S T p. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> ((p::name prm) \<bullet> \<Psi>', p \<bullet> S, p \<bullet> T) \<in> Rel"
  and     Assoc: "\<And>\<Psi>' S T U. (\<Psi>', S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"
  and     ParPres: "\<And>\<Psi>' S T U. (\<Psi>', S, T) \<in> Rel \<Longrightarrow> (\<Psi>', S \<parallel> U, T \<parallel> U) \<in> Rel"
  and     FrameParPres: "\<And>\<Psi>' \<Psi>\<^sub>U S T U A\<^sub>U. \<lbrakk>(\<Psi>' \<otimes> \<Psi>\<^sub>U, S, T) \<in> Rel; extractFrame U = \<langle>A\<^sub>U, \<Psi>\<^sub>U\<rangle>; A\<^sub>U \<sharp>* \<Psi>'; A\<^sub>U \<sharp>* S; A\<^sub>U \<sharp>* T\<rbrakk> \<Longrightarrow>
                                            (\<Psi>', U \<parallel> S, U \<parallel> T) \<in> Rel"
  and     ResPres: "\<And>\<Psi>' S T xvec. \<lbrakk>(\<Psi>', S, T) \<in> Rel; xvec \<sharp>* \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>S, \<lparr>\<nu>*xvec\<rparr>T) \<in> Rel"
  and     ScopeExt: "\<And>xvec \<Psi>' S T. \<lbrakk>xvec \<sharp>* \<Psi>'; xvec \<sharp>* T\<rbrakk> \<Longrightarrow> (\<Psi>', \<lparr>\<nu>*xvec\<rparr>(S \<parallel> T), (\<lparr>\<nu>*xvec\<rparr>S) \<parallel> T) \<in> Rel"
  and     Trans: "\<And>\<Psi>' S T U. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, U) \<in> Rel"
  and     Compose: "\<And>\<Psi>' S T U O. \<lbrakk>(\<Psi>', S, T) \<in> Rel; (\<Psi>', T, U) \<in> Rel'; (\<Psi>', U, O) \<in> Rel\<rbrakk> \<Longrightarrow> (\<Psi>', S, O) \<in> Rel'"
  and     C1: "\<And>\<Psi> S T U. \<lbrakk>(\<Psi>, S, T) \<in> Rel; guarded S; guarded T\<rbrakk> \<Longrightarrow> (\<Psi>, U \<parallel> !S, U \<parallel> !T) \<in> Rel'"
  and     Der: "\<And>\<Psi>' S \<alpha> S' T. \<lbrakk>\<Psi>' \<rhd> !S \<longmapsto>\<alpha> \<prec> S'; (\<Psi>', S, T) \<in> Rel; bn \<alpha> \<sharp>* \<Psi>'; bn \<alpha> \<sharp>* S; bn \<alpha> \<sharp>* T; guarded T; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow>
                                      \<exists>T' U O.  \<Psi>' \<rhd> !T \<longmapsto>\<alpha> \<prec> T' \<and> (\<Psi>', S', U \<parallel> !S) \<in> Rel \<and> (\<Psi>', T', O \<parallel> !T) \<in> Rel \<and>
                                                (\<Psi>', U, O) \<in> Rel \<and> ((supp U)::name set) \<subseteq> supp S' \<and> 
                                                 ((supp O)::name set) \<subseteq> supp T'"

  shows "\<Psi> \<rhd> R \<parallel> !P \<leadsto>[Rel'] R \<parallel> !Q"
using \<open>eqvt Rel'\<close>
proof(induct rule: simI[of _ _ _ _ "()"])
  case(cSim \<alpha> RQ')
  from \<open>bn \<alpha> \<sharp>* (R \<parallel> !P)\<close> \<open>bn \<alpha> \<sharp>* (R \<parallel> !Q)\<close> have "bn \<alpha> \<sharp>* P" and "bn \<alpha> \<sharp>* (!Q)" and "bn \<alpha> \<sharp>* Q" and "bn \<alpha> \<sharp>* R" by simp+
  from \<open>\<Psi> \<rhd> R \<parallel> !Q \<longmapsto>\<alpha> \<prec> RQ'\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close> \<open>bn \<alpha> \<sharp>* R\<close> \<open>bn \<alpha> \<sharp>* !Q\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> show ?case
  proof(induct rule: parCases[where C=P])
    case(cPar1 R' A\<^sub>Q \<Psi>\<^sub>Q)
    from \<open>extractFrame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = SBottom'" by simp+
    with \<open>\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>\<alpha> \<prec> R'\<close> \<open>bn \<alpha> \<sharp>* P\<close> have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<alpha> \<prec> (R' \<parallel> !P)"
      by(rule_tac Par1) (assumption | simp)+
    moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> have "(\<Psi>, R' \<parallel> !P, R' \<parallel> !Q) \<in> Rel'"
      by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 Q' A\<^sub>R \<Psi>\<^sub>R)
    have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>\<alpha> \<prec> Q'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    with \<open>bn \<alpha> \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> have "bn \<alpha> \<sharp>* \<Psi>\<^sub>R" by(force dest: extractFrameFreshChain)
    with QTrans \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>bn \<alpha> \<sharp>* \<Psi>\<close>\<open>bn \<alpha> \<sharp>* P\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>guarded P\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close>
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>\<alpha> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      by(drule_tac cSym) (auto dest: Der cExt)
    from PTrans FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> \<open>bn \<alpha> \<sharp>* R\<close> have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<alpha> \<prec> (R \<parallel> P')"
      by(rule_tac Par2) auto
    moreover 
    { 
      from \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* (!Q)\<close> \<open>A\<^sub>R \<sharp>* \<alpha>\<close> PTrans QTrans \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close> have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'"
        by(force dest: freeFreshChainDerivative)+
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel\<close> FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>R \<sharp>* P\<close> suppT have "(\<Psi>, R \<parallel> P', R \<parallel> (T \<parallel> !P)) \<in> Rel"
        by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> P', (R \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> have "(\<Psi>, (R \<parallel> T) \<parallel> !P, (R \<parallel> T) \<parallel> !Q) \<in> Rel'"
        by(rule C1)
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel\<close> \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', T \<parallel> !Q) \<in> Rel"
        by(blast intro: ParPres Trans)
      with FrR \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P'\<close> \<open>A\<^sub>R \<sharp>* Q'\<close> \<open>A\<^sub>R \<sharp>* (!Q)\<close> suppT suppS have "(\<Psi>, R \<parallel> Q', R \<parallel> (T \<parallel> !Q)) \<in> Rel"
        by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R \<parallel> Q', (R \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      ultimately have "(\<Psi>, R \<parallel> P', R \<parallel> Q') \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  next
    case(cComm1 \<Psi>\<^sub>Q M N R' A\<^sub>R \<Psi>\<^sub>R K xvec Q' A\<^sub>Q)
    from \<open>extractFrame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = SBottom'" by simp+
    have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>N\<rparr> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by fact
    from FrR \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> have "xvec \<sharp>* \<Psi>\<^sub>R" by(force dest: extractFrameFreshChain)
    with QTrans \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>xvec \<sharp>* \<Psi>\<close>\<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* (!Q)\<close> \<open>guarded P\<close> \<open>xvec \<sharp>* K\<close>
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp Q'"
      by(drule_tac cSym) (fastforce dest: Der intro: cExt)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P')" 
      using PTrans \<open>\<Psi>\<^sub>Q = SBottom'\<close> \<open>xvec \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* P\<close>
      by(rule_tac Comm1) (assumption | simp)+

    moreover from \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* (!Q)\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> PTrans QTrans \<open>xvec \<sharp>* K\<close> \<open>distinct xvec\<close> 
    have "A\<^sub>R \<sharp>* P'" and "A\<^sub>R \<sharp>* Q'" by(force dest: outputFreshChainDerivative)+
    moreover with RTrans FrR \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* (!Q)\<close> \<open>A\<^sub>R \<sharp>* M\<close>
    obtain \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* \<Psi>"
                         and "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q"
      by(rule_tac C="(\<Psi>, P, P', Q, Q')" and C'=\<Psi> in expandFrame) auto

    moreover 
    { 
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel\<close> have "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', P', T \<parallel> !P) \<in> Rel" by(rule cExt)
      with \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', P', T \<parallel> !P) \<in> Rel"
        by(metis Associativity StatEq compositionSym) 
      with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* P\<close> suppT have "(\<Psi>, R' \<parallel> P', R' \<parallel> (T \<parallel> !P)) \<in> Rel"
        by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> P', (R' \<parallel> T) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P) \<in> Rel"
        by(metis ResPres psiFreshVec ScopeExt Trans)
      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel'"
        by(rule C1)
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', S \<parallel> !Q) \<in> Rel\<close> \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R, Q', T \<parallel> !Q) \<in> Rel"
        by(blast intro: ParPres Trans)
      hence "((\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>', Q', T \<parallel> !Q) \<in> Rel" by(rule cExt)
      with \<open>\<Psi>\<^sub>R \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', Q', T \<parallel> !Q) \<in> Rel"
        by(metis Associativity StatEq compositionSym) 
      with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> suppT suppS have "(\<Psi>, R' \<parallel> Q', R' \<parallel> (T \<parallel> !Q)) \<in> Rel"
        by(rule_tac FrameParPres) (auto simp add: fresh_star_def fresh_def psi.supp)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> T) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* (!Q)\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> T)) \<parallel> !Q) \<in> Rel"
        by(metis ResPres psiFreshVec ScopeExt Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  next
    case(cComm2 \<Psi>\<^sub>Q M xvec N R' A\<^sub>R \<Psi>\<^sub>R K Q' A\<^sub>Q)
    from \<open>extractFrame (!Q) = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> have "A\<^sub>Q = []" and "\<Psi>\<^sub>Q = SBottom'" by simp+
    have RTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> R'" and FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" by fact+
    then obtain p \<Psi>' A\<^sub>R' \<Psi>\<^sub>R' where S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
                                and FrR': "extractFrame R' = \<langle>A\<^sub>R', \<Psi>\<^sub>R'\<rangle>" and "(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'" and "A\<^sub>R' \<sharp>* \<Psi>"
                                and "A\<^sub>R' \<sharp>* N" and "A\<^sub>R' \<sharp>* R'" and "A\<^sub>R' \<sharp>* P" and "A\<^sub>R' \<sharp>* Q" and "(p \<bullet> xvec) \<sharp>* \<Psi>"
                                and "(p \<bullet> xvec) \<sharp>* P" and "(p \<bullet> xvec) \<sharp>* Q" and "xvec \<sharp>* A\<^sub>R'" and "(p \<bullet> xvec) \<sharp>* A\<^sub>R'"
                                and "distinctPerm p" and "(p \<bullet> xvec) \<sharp>* R'" and "(p \<bullet> xvec) \<sharp>* N" 
      using \<open>distinct A\<^sub>R\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* xvec\<close> \<open>A\<^sub>R \<sharp>* N\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* (!Q)\<close>
            \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>xvec \<sharp>* (!Q)\<close> \<open>xvec \<sharp>* R\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
     by(rule_tac C="(\<Psi>, P, Q)" and C'="(\<Psi>, P, Q)" in expandFrame) (assumption | simp)+

    from RTrans S \<open>(p \<bullet> xvec) \<sharp>* N\<close> \<open>(p \<bullet> xvec) \<sharp>* R'\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> R \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> R')"
      apply(simp add: residualInject)
      by(subst boundOutputChainAlpha''[symmetric]) auto

    moreover have QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by fact
    with QTrans S \<open>(p \<bullet> xvec) \<sharp>* N\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !Q \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> (p \<bullet> Q')" using \<open>distinctPerm p\<close> \<open>xvec \<sharp>* (!Q)\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close>
      by(rule_tac inputAlpha) auto
    with \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close>
    obtain P' S T where PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> !P \<longmapsto>K\<lparr>(p \<bullet> N)\<rparr> \<prec> P'" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel"
                    and "(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel" and "(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel"
                    and suppT: "((supp T)::name set) \<subseteq> supp P'" and suppS: "((supp S)::name set) \<subseteq> supp(p \<bullet> Q')"
      by(drule_tac cSym) (auto dest: Der cExt)
    note \<open>\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close>
    ultimately have "\<Psi> \<rhd> R \<parallel> !P \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P')" 
      using PTrans FrR \<open>\<Psi>\<^sub>Q = SBottom'\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>A\<^sub>R \<sharp>* P\<close>
      by(rule_tac Comm2) (assumption | simp)+

    moreover from \<open>A\<^sub>R' \<sharp>* P\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> \<open>A\<^sub>R' \<sharp>* N\<close> S \<open>xvec \<sharp>* A\<^sub>R'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>R'\<close> PTrans QTrans \<open>distinctPerm p\<close> have "A\<^sub>R' \<sharp>* P'" and "A\<^sub>R' \<sharp>* Q'"
      apply -
      apply(drule_tac inputFreshChainDerivative, auto)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(force dest: inputFreshChainDerivative)+
    from \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* N\<close> PTrans \<open>distinctPerm p\<close> have "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
      apply(drule_tac inputFreshChainDerivative, simp)
      apply(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)
      by(subst pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst, symmetric, of _ _ p], simp)

    { 
      from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, P', T \<parallel> !P) \<in> Rel\<close> have "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R), (p \<bullet> P'), p \<bullet> (T \<parallel> !P)) \<in> Rel"
        by(rule Closed)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> \<open>(p \<bullet> xvec) \<sharp>* P\<close> S have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel"
        by(simp add: eqvts)     
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', p \<bullet> P', (p \<bullet> T) \<parallel> !P) \<in> Rel" by(rule cExt)
      with \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', (p \<bullet> P'), (p \<bullet> T) \<parallel> !P) \<in> Rel"
        by(metis Associativity StatEq compositionSym) 
      with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* P\<close> \<open>xvec \<sharp>* A\<^sub>R'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>R'\<close> S \<open>distinctPerm p\<close> suppT
      have "(\<Psi>, R' \<parallel> (p \<bullet> P'), R' \<parallel> ((p \<bullet> T) \<parallel> !P)) \<in> Rel"
        apply(rule_tac FrameParPres)
        apply(assumption | simp add: freshChainSimps)+
        by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> (p \<bullet> P'), (R' \<parallel> (p \<bullet> T)) \<parallel> !P) \<in> Rel" by(blast intro: Assoc Trans)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* P\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> P')), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
        by(metis ResPres psiFreshVec ScopeExt Trans)
      hence "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P) \<in> Rel"
      using \<open>(p \<bullet> xvec) \<sharp>* R'\<close> \<open>(p \<bullet> xvec) \<sharp>* (p \<bullet> P')\<close> S \<open>distinctPerm p\<close>
      apply(erule_tac rev_mp) by(subst resChainAlpha[of p]) auto
      moreover from \<open>(\<Psi>, P, Q) \<in> Rel\<close> \<open>guarded P\<close> \<open>guarded Q\<close> have "(\<Psi>, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !P, (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel'"
        by(rule C1)
      moreover from \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), S \<parallel> !Q) \<in> Rel\<close> \<open>(\<Psi> \<otimes> \<Psi>\<^sub>R, S, T) \<in> Rel\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R, (p \<bullet> Q'), T \<parallel> !Q) \<in> Rel"
        by(blast intro: ParPres Trans)
      hence "(p \<bullet> (\<Psi> \<otimes> \<Psi>\<^sub>R), p \<bullet> p \<bullet> Q', p \<bullet> (T \<parallel> !Q)) \<in> Rel" by(rule Closed)
      with S \<open>xvec \<sharp>* \<Psi>\<close> \<open>(p \<bullet> xvec) \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* (!Q)\<close> \<open>(p \<bullet> xvec) \<sharp>* Q\<close> \<open>distinctPerm p\<close>
      have "(\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R), Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(simp add: eqvts)
      hence "((\<Psi> \<otimes> (p \<bullet> \<Psi>\<^sub>R)) \<otimes> \<Psi>', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel" by(rule cExt)
      with \<open>(p \<bullet> \<Psi>\<^sub>R) \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>R'\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>R', Q', (p \<bullet> T) \<parallel> !Q) \<in> Rel"
        by(metis Associativity StatEq compositionSym) 
      with FrR' \<open>A\<^sub>R' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R' \<sharp>* P'\<close> \<open>A\<^sub>R' \<sharp>* Q'\<close> \<open>A\<^sub>R' \<sharp>* Q\<close> suppT suppS \<open>xvec \<sharp>* A\<^sub>R'\<close> \<open>(p \<bullet> xvec) \<sharp>* A\<^sub>R'\<close> S \<open>distinctPerm p\<close> 
      have "(\<Psi>, R' \<parallel> Q', R' \<parallel> ((p \<bullet> T) \<parallel> !Q)) \<in> Rel"
        apply(rule_tac FrameParPres)
        apply(assumption | simp)+
        apply(simp add: freshChainSimps)
        by(auto simp add: fresh_star_def fresh_def)
      hence "(\<Psi>, R' \<parallel> Q', (R' \<parallel> (p \<bullet> T)) \<parallel> !Q) \<in> Rel" by(blast intro: Assoc Trans)
      with \<open>xvec \<sharp>* \<Psi>\<close> \<open>xvec \<sharp>* (!Q)\<close> have "(\<Psi>, \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q'), (\<lparr>\<nu>*xvec\<rparr>(R' \<parallel> (p \<bullet> T))) \<parallel> !Q) \<in> Rel"
        by(metis ResPres psiFreshVec ScopeExt Trans)
      ultimately have "(\<Psi>, \<lparr>\<nu>*(p \<bullet> xvec)\<rparr>((p \<bullet> R') \<parallel> P'), \<lparr>\<nu>*xvec\<rparr>(R' \<parallel> Q')) \<in> Rel'" by(blast intro: cSym Compose)
    }
    ultimately show ?case by blast
  qed
qed
notation relcomp (infixr "O" 75)
end

end
