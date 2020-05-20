(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Pres
  imports Weak_Psi_Congruence Weak_Cong_Sim_Pres Weak_Bisim_Pres
begin

context env begin

lemma weakPsiCongInputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "\<And>Tvec. length xvec = length Tvec \<Longrightarrow>  \<Psi> \<rhd> P[xvec::=Tvec] \<approx> Q[xvec::=Tvec]"

  shows "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<doteq> M\<lparr>\<lambda>*xvec N\<rparr>.Q"
proof -
  from assms have "\<forall>Tvec. length xvec = length Tvec \<longrightarrow>  \<Psi> \<rhd> P[xvec::=Tvec] \<approx> Q[xvec::=Tvec]"
    by simp
  thus ?thesis
  proof(induct rule: weakPsiCongSymI)
    case(cSym P Q)
    thus ?case by(auto dest: weakBisimE)
  next
    case(cSim P Q)
    show ?case 
      by(induct rule: weakCongSimI) auto
  next
    case(cWeakBisim P Q)
    thus ?case by(rule_tac weakBisimInputPres) auto
  qed
qed
  
lemma weakPsiCongOutputPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a

  assumes "\<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<doteq> M\<langle>N\<rangle>.Q"
using assms
proof(induct rule: weakPsiCongSymI)
  case(cSym P Q)
  thus ?case by(rule weakPsiCongSym)
next
  case(cSim P Q)
  show ?case by(induct rule: weakCongSimI) auto
next
  case(cWeakBisim P Q)
  thus ?case by(metis weakPsiCongE weakBisimOutputPres)
qed

lemma weakBisimCasePres:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes A: "\<And>\<phi> P. (\<phi>, P) mem CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"
  and     B: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"

  shows "\<Psi> \<rhd> Cases CsP \<approx> Cases CsQ"
proof -
  let ?X = "{(\<Psi>, Cases CsP, Cases CsQ) | \<Psi> CsP CsQ. (\<forall>\<phi> P. (\<phi>, P) mem CsP \<longrightarrow> (\<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q))) \<and>
                                                     (\<forall>\<phi> Q. (\<phi>, Q) mem CsQ \<longrightarrow> (\<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)))}"
  from assms have "(\<Psi>, Cases CsP, Cases CsQ) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cStatImp \<Psi> CasesP CasesQ)
    thus ?case
      apply(auto simp add: weakStatImp_def)
      by(rule_tac x="Cases CsQ" in exI, auto)
  next
    case(cSim \<Psi> CasesP CasesQ)
    then obtain CsP CsQ where C1: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"
                          and A: "CasesP = Cases CsP" and B: "CasesQ = Cases CsQ"
      by auto
    note C1
    moreover have "\<And>\<Psi> P Q. \<Psi> \<rhd> P \<approx> Q \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><weakBisim> Q" by(rule weakBisimE)
    moreover note weakPsiCongE(1) weakPsiCongE(2)
    ultimately have "\<Psi> \<rhd> Cases CsP \<leadsto><weakBisim> Cases CsQ"
      by(rule_tac caseWeakSimPres) (assumption | blast)+
    hence "\<Psi> \<rhd> Cases CsP \<leadsto><(?X \<union> weakBisim)> Cases CsQ"
      by(rule_tac weakSimMonotonic) auto
    with A B show ?case by blast
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by auto
  next
    case(cSym \<Psi> P Q)
    thus ?case by auto (metis weakPsiCongSym)+
  qed
qed

lemma weakPsiCongCasePres:
  fixes \<Psi>   :: 'b
  and   CsP :: "('c \<times> ('a, 'b, 'c) psi) list"
  and   CsQ :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes A: "\<And>\<phi> P. (\<phi>, P) mem CsP \<Longrightarrow> \<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"
  and     B: "\<And>\<phi> Q. (\<phi>, Q) mem CsQ \<Longrightarrow> \<exists>P. (\<phi>, P) mem CsP \<and> guarded P \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q)"

  shows "\<Psi> \<rhd> Cases CsP \<doteq> Cases CsQ"
proof -
  let ?Prop = "\<lambda>CsP CsQ. \<forall>\<phi> P. (\<phi>, P) mem CsP \<longrightarrow> (\<exists>Q. (\<phi>, Q) mem CsQ \<and> guarded Q \<and> (\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q))"
  from A B have "?Prop CsP CsQ \<and> ?Prop CsQ CsP" by(metis weakPsiCongSym)
  thus ?thesis
  proof(induct rule: weakPsiCongSymI[where C="\<lambda>P. Cases P"])
    case(cSym P Q)
    thus ?case by auto
  next
    case(cWeakBisim CsP CsQ)
    thus ?case
      by(rule_tac weakBisimCasePres) (metis weakPsiCongSym)+
  next
    case(cSim CsP CsQ)
    thus ?case       
      apply auto
      apply(rule_tac weakCongSimCasePres, auto)
      by(blast dest: weakPsiCongE)
  qed
qed

lemma weakPsiCongResPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   x :: name
  
  assumes "\<Psi> \<rhd> P \<doteq> Q"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<doteq> \<lparr>\<nu>x\<rparr>Q"
using \<open>\<Psi> \<rhd> P \<doteq> Q\<close>
proof(induct rule: weakPsiCongSymI)
  case(cSym P Q)
  thus ?case by(rule weakPsiCongSym)
next
  case(cWeakBisim P Q)
  thus ?case using \<open>x \<sharp> \<Psi>\<close> by(metis weakPsiCongE weakBisimResPres)
next
  case(cSim P Q)
  obtain y::name where "y \<sharp> \<Psi>" and "y \<sharp> P" and "y \<sharp> Q"
    by(generate_fresh "name") auto
  from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<doteq> ([(x, y)] \<bullet> Q)" by(rule weakPsiCongClosed)
  hence "([(x, y)] \<bullet> \<Psi>) \<rhd> ([(x, y)] \<bullet> P) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, y)] \<bullet> Q)" by(rule weakPsiCongE)
  with \<open>x \<sharp> \<Psi>\<close> \<open>y \<sharp> \<Psi>\<close> have "\<Psi>  \<rhd> ([(x, y)] \<bullet> P) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, y)] \<bullet> Q)" by simp
  moreover have "eqvt weakBisim" by simp
  moreover note \<open>y \<sharp> \<Psi>\<close>
  moreover have "weakBisim \<subseteq> weakBisim" by auto
  moreover note weakBisimResPres
  ultimately have "\<Psi> \<rhd> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> P) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> \<lparr>\<nu>y\<rparr>([(x, y)] \<bullet> Q)" by(rule weakCongSimResPres)
  with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> show ?case by(simp add: alphaRes)
qed

lemma weakPsiCongResChainPres:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<doteq> Q"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<doteq> \<lparr>\<nu>*xvec\<rparr>Q"
using assms
by(induct xvec) (auto intro: weakPsiCongResPres)

lemma weakPsiCongParPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"
  
  assumes "\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> P \<parallel> R \<doteq> Q \<parallel> R"
using assms
proof(induct rule: weakPsiCongSymI[where C="\<lambda>P. P \<parallel> R"])
  case(cSym P Q)
  thus ?case by(blast dest: weakPsiCongSym)
next
  case(cWeakBisim P Q)
  thus ?case by(metis weakBisimParPres weakPsiCongE)
next
  case(cSim P Q)
  {
    fix \<Psi>
    from \<open>\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(auto dest: weakPsiCongE)
  }
  moreover {
    fix \<Psi>
    from \<open>\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<leadsto><weakBisim> Q" by(auto dest: weakPsiCongE weakBisimE)
  }
  moreover {
    fix \<Psi>
    from \<open>\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<approx> Q" by(auto dest: weakPsiCongE)
    hence "\<Psi> \<rhd> Q \<lessapprox><weakBisim> P" by(metis weakBisimE)
  }
  ultimately show ?case using weakBisimEqvt weakBisimEqvt weakBisimE(4)  weakBisimE(3) weakBisimParPresAux weakBisimResChainPres statEqWeakBisim
    by(rule_tac weakCongSimParPres)
qed

end

end
