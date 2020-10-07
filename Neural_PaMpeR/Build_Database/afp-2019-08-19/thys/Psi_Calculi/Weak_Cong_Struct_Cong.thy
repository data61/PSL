(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Struct_Cong
  imports Weak_Cong_Pres Weak_Bisim_Struct_Cong
begin

context env begin

lemma weakPsiCongParComm:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  
  shows "\<Psi> \<rhd> P \<parallel> Q \<doteq> Q \<parallel> P"
by(metis bisimParComm strongBisimWeakPsiCong)

lemma weakPsiCongResComm:
  fixes x :: name
  and   \<Psi> :: 'b
  and   y :: name
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "y \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<doteq> \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(metis bisimResComm strongBisimWeakPsiCong)

lemma weakPsiCongResComm':
  fixes x    :: name
  and   \<Psi>   :: 'b
  and   xvec :: "name list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(\<lparr>\<nu>*xvec\<rparr>P) \<doteq> \<lparr>\<nu>*xvec\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(metis bisimResComm' strongBisimWeakPsiCong)

lemma weakPsiCongScopeExt:
  fixes x :: name
  and   \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<doteq> P \<parallel> \<lparr>\<nu>x\<rparr>Q"
using assms
by(metis bisimScopeExt strongBisimWeakPsiCong)

lemma weakPsiCongScopeExtChain:
  fixes xvec :: "name list"
  and   \<Psi>    :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<doteq> P \<parallel> (\<lparr>\<nu>*xvec\<rparr>Q)"
using assms
by(metis bisimScopeExtChain strongBisimWeakPsiCong)

lemma weakPsiCongParAssoc:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> (P \<parallel> Q) \<parallel> R \<doteq> P \<parallel> (Q \<parallel> R)"
by(metis bisimParAssoc strongBisimWeakPsiCong)

lemma weakPsiCongParNil:
  fixes P :: "('a, 'b, 'c) psi"

  shows "\<Psi> \<rhd> P \<parallel> \<zero> \<doteq> P"
by(metis bisimParNil strongBisimWeakPsiCong)

lemma weakPsiCongResNil:
  fixes x :: name
  and   \<Psi> :: 'b
  
  assumes "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>\<zero> \<doteq> \<zero>"
using assms
by(metis bisimResNil strongBisimWeakPsiCong)

lemma weakPsiCongOutputPushRes:
  fixes x :: name
  and   \<Psi> :: 'b
  and   M :: 'a
  and   N :: 'a
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<langle>N\<rangle>.P) \<doteq> M\<langle>N\<rangle>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis bisimOutputPushRes strongBisimWeakPsiCong)

lemma weakPsiCongInputPushRes:
  fixes x    :: name
  and   \<Psi>    :: 'b
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> N"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(M\<lparr>\<lambda>*xvec N\<rparr>.P) \<doteq> M\<lparr>\<lambda>*xvec N\<rparr>.\<lparr>\<nu>x\<rparr>P"
using assms
by(metis bisimInputPushRes strongBisimWeakPsiCong)

lemma weakPsiCongCasePushRes:
  fixes x  :: name
  and   \<Psi>  :: 'b
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> (map fst Cs)"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(Cases Cs) \<doteq> Cases(map (\<lambda>(\<phi>, P). (\<phi>, \<lparr>\<nu>x\<rparr>P)) Cs)"
using assms
by(metis bisimCasePushRes strongBisimWeakPsiCong)

lemma weakBangExt:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  
  assumes "guarded P"

  shows "\<Psi> \<rhd> !P \<doteq> P \<parallel> !P"
using assms
by(metis bangExt strongBisimWeakPsiCong)

lemma weakPsiCongParSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<doteq> R \<parallel> Q"
using assms
by(metis weakPsiCongParComm weakPsiCongParPres weakPsiCongTransitive)

lemma weakPsiCongScopeExtSym:
  fixes x :: name
  and   Q :: "('a, 'b, 'c) psi"
  and   P :: "('a, 'b, 'c) psi"

  assumes "x \<sharp> \<Psi>"
  and     "x \<sharp> Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<doteq> (\<lparr>\<nu>x\<rparr>P) \<parallel> Q"
using assms
by(metis weakPsiCongScopeExt weakPsiCongTransitive weakPsiCongParComm weakPsiCongE weakPsiCongResPres)

lemma weakPsiCongScopeExtChainSym:
  fixes xvec :: "name list"
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "xvec \<sharp>* \<Psi>"
  and     "xvec \<sharp>* Q"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>(P \<parallel> Q) \<doteq> (\<lparr>\<nu>*xvec\<rparr>P) \<parallel> Q"
using assms
by(induct xvec) (auto intro: weakPsiCongScopeExtSym weakPsiCongReflexive weakPsiCongTransitive weakPsiCongResPres)

lemma weakPsiCongParPresSym:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<And>\<Psi>. \<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> R \<parallel> P \<doteq> R \<parallel> Q"
using assms
by(metis weakPsiCongParComm weakPsiCongParPres weakPsiCongTransitive)

lemma tauCongChainBangI:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "guarded P"

  obtains Q where "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q" and "\<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
proof -
  assume "\<And>Q. \<lbrakk>\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q; \<Psi> \<rhd> Q \<sim> P' \<parallel> !P\<rbrakk> \<Longrightarrow> thesis"
  moreover from \<open>\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sub>\<tau> P'\<close> have "\<exists>Q. \<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q \<and> \<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
  proof(induct x1=="P \<parallel> P" P' rule: tauStepChainInduct)
    case(TauBase R')
    from \<open>\<Psi> \<rhd> P \<parallel> P \<longmapsto>\<tau> \<prec> R'\<close>
    obtain Q where "\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> Q" and "Q \<sim> R' \<parallel> !P" using \<open>guarded P\<close> 
      by(rule tauBangI)
    from \<open>\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> Q\<close> have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q" by auto
    moreover from \<open>Q \<sim> R' \<parallel> !P\<close> have "\<Psi> \<rhd> Q \<sim> R' \<parallel> !P"
      apply(drule_tac bisimE(3)[where \<Psi>'=\<Psi>])
      by(rule_tac statEqBisim, assumption) (metis Identity AssertionStatEqSym AssertionStatEqTrans Commutativity)
    ultimately show ?case by blast
  next
    case(TauStep R' R'')
    then obtain Q where PChain: "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q" and "\<Psi> \<rhd> Q \<sim> R' \<parallel> !P" by auto
    from \<open>\<Psi> \<rhd> R' \<longmapsto>\<tau> \<prec> R''\<close> have "\<Psi> \<otimes> \<one> \<rhd> R' \<longmapsto>\<tau> \<prec> R''" by(rule statEqTransition) (metis Identity AssertionStatEqSym)
    hence "\<Psi> \<rhd> R' \<parallel> !P \<longmapsto>\<tau> \<prec> R'' \<parallel> !P" by(rule_tac Par1) auto
    with \<open>\<Psi> \<rhd> Q \<sim> R' \<parallel> !P\<close> obtain Q' where QTrans: "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" and "\<Psi> \<rhd> Q' \<sim> R'' \<parallel> !P"
      by(force dest: bisimE(2) simE)
    from PChain QTrans have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q'" by(auto dest: tauActTauStepChain)
    thus ?case using \<open>\<Psi> \<rhd> Q' \<sim> R'' \<parallel> !P\<close> by blast
  qed
  ultimately show ?thesis by blast
qed

lemma weakPsiCongBangPres:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes PeqQ: "\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q"
  and     "guarded P"
  and     "guarded Q"

  shows   "\<Psi> \<rhd> !P \<doteq> !Q"
proof -
  from assms have "(\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q) \<and> guarded P \<and> guarded Q" by auto
  hence "\<Psi> \<rhd> \<zero> \<parallel> !P \<doteq> \<zero> \<parallel> !Q"
  proof(induct rule: weakPsiCongSymI[where C="\<lambda>P. \<zero> \<parallel> !P"])
    case(cSym P Q)
    thus ?case by(auto dest: weakPsiCongSym)
  next
    case(cWeakBisim P Q)
    thus ?case by(metis weakPsiCongE weakBisimBangPresAux)
  next
    case(cSim P Q)
    then have "\<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q" and "guarded P" and "guarded Q" by auto
    moreover hence "\<Psi> \<rhd> P \<approx> Q" by(metis weakPsiCongE weakBisimE)
    moreover have "\<And>\<Psi> P Q. (\<forall>\<Psi>. (\<Psi> \<rhd> P \<doteq> Q)) \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
      by(blast dest: weakPsiCongE)
    moreover note weakBisimClosed bisimClosed weakBisimE(3) bisimE(3) weakBisimE(2) 
                  weakBisimE(4) bisimE(4) statEqWeakBisim statEqBisim weakBisimTransitive bisimTransitive weakBisimParAssoc[THEN weakBisimE(4)]
                  bisimParAssoc[THEN bisimE(4)] weakBisimParPres
    moreover have "\<And>P Q. \<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q \<Longrightarrow> \<forall>\<Psi>. \<Psi> \<rhd> P \<parallel> P \<doteq> Q \<parallel> Q"
      by(metis weakPsiCongParPres weakPsiCongParComm weakPsiCongSym weakPsiCongTransitive)
    moreover note bisimParPresSym
    moreover from strongBisimWeakBisim have "bisim \<subseteq> weakBisim" by auto
    moreover have "\<And>\<Psi> \<Psi>\<^sub>R P Q R A\<^sub>R. \<lbrakk>\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> P \<approx> Q; extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>; A\<^sub>R \<sharp>* \<Psi>; A\<^sub>R \<sharp>* P; A\<^sub>R \<sharp>* Q\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> R \<parallel> P \<approx> R \<parallel> Q"
      by(metis weakBisimParComm weakBisimTransitive weakBisimParPresAux)
    moreover note weakBisimResChainPres bisimResChainPres weakBisimScopeExtChainSym bisimScopeExtChainSym
    moreover have "\<And>\<Psi> P R S Q. \<lbrakk>\<Psi> \<rhd> P \<approx> R; \<Psi> \<rhd> R \<approx> S; \<Psi> \<rhd> S \<sim> Q\<rbrakk> \<Longrightarrow> \<Psi> \<rhd> P \<approx> Q"
      by(blast dest: weakBisimTransitive strongBisimWeakBisim)
    moreover note weakBisimBangPresAux
    moreover from bangActE have "\<And>\<Psi> P \<alpha> P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'; bn \<alpha> \<sharp>* P; guarded P; \<alpha> \<noteq> \<tau>; bn \<alpha> \<sharp>* subject \<alpha>\<rbrakk> \<Longrightarrow> \<exists>Q. \<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
      by blast
    moreover from bangTauE have "\<And>\<Psi> P P'. \<lbrakk>\<Psi> \<rhd> !P \<longmapsto>\<tau> \<prec> P'; guarded P\<rbrakk> \<Longrightarrow> \<exists>Q. \<Psi> \<rhd> P \<parallel> P \<longmapsto>\<tau> \<prec> Q \<and> P' \<sim> Q \<parallel> !P"
      by blast
    moreover from tauCongChainBangI have "\<And>\<Psi> P P'. \<lbrakk>\<Psi> \<rhd> P \<parallel> P \<Longrightarrow>\<^sub>\<tau> P'; guarded P\<rbrakk> \<Longrightarrow> \<exists>Q. \<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> Q \<and> \<Psi> \<rhd> Q \<sim> P' \<parallel> !P"
      by blast
    ultimately show ?case
      by(rule_tac weakCongSimBangPres[where Rel=weakBisim and Rel'=bisim and Rel''=weakBisim and Eq="\<lambda>P Q. \<forall>\<Psi>. \<Psi> \<rhd> P \<doteq> Q"])
  qed
  thus ?thesis
    by(metis weakPsiCongParNil weakPsiCongParComm weakPsiCongTransitive weakPsiCongSym)
qed

end

end
