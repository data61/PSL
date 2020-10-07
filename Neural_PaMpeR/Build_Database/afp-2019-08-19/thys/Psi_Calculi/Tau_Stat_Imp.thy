(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Stat_Imp
  imports Tau_Sim Weaken_Stat_Imp
begin

locale weakTauLaws = weak + tau
begin

lemma tauLaw1StatImpLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<lessapprox>\<^sub>w<Rel> Q"
  and     "(\<Psi>, \<tau>.(P), Q) \<in> Rel"
 
  shows "\<Psi> \<rhd> \<tau>.(P) \<lessapprox>\<^sub>w<Rel> Q"
proof -
  have "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q" by simp
  moreover have "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>" by(rule insertTauAssertion)
  hence "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
    by(metis FrameStatImpTrans FrameStatEq_def insertAssertionWeaken)
  ultimately show ?thesis using \<open>(\<Psi>, \<tau>.(P), Q) \<in> Rel\<close>
    by(rule weakenStatImpI)
qed

lemma tauLaw1StatImpRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<lessapprox><Rel> Q"
  and     C1: "\<And>\<Psi> P Q R. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; \<Psi> \<rhd> Q \<sim> R\<rbrakk> \<Longrightarrow> (\<Psi>, P, R) \<in> Rel'"

  shows "\<Psi> \<rhd> P \<lessapprox><Rel'> \<tau>.(Q)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  from \<open>\<Psi> \<rhd> P \<lessapprox><Rel> Q\<close> obtain Q' Q'' 
    where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'" and PImpQ': "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q') \<Psi>" 
      and Q'Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''" and PRelQ'': "(\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel"
    by(rule weakStatImpE)
    
  obtain Q''' where QTrans: "\<Psi> \<rhd> \<tau>.(Q) \<longmapsto>\<tau> \<prec> Q'''" and "\<Psi> \<rhd> Q \<sim> Q'''" using tauActionI by auto
  
  from \<open>\<Psi> \<rhd> Q \<sim> Q'''\<close> QChain bisimE(2) obtain Q'''' where Q'''Chain: "\<Psi> \<rhd> Q''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''" and "\<Psi> \<rhd> Q' \<sim> Q''''"
    by(metis bisimE(4) simTauChain)
  
  from QTrans Q'''Chain have "\<Psi> \<rhd> \<tau>.(Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''''" by(drule_tac tauActTauChain) auto
  moreover from \<open>\<Psi> \<rhd> Q' \<sim> Q''''\<close> have "insertAssertion (extractFrame Q') \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'''') \<Psi>"
    by(metis bisimE FrameStatEq_def)
  with PImpQ'  have "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'''') \<Psi>"
    by(rule FrameStatImpTrans)
  moreover from \<open>\<Psi> \<rhd> Q' \<sim> Q''''\<close> have "\<Psi> \<otimes> \<Psi>' \<rhd> Q' \<sim> Q''''" by(rule bisimE) 
  then obtain Q''''' where Q''''Chain: "\<Psi> \<otimes> \<Psi>' \<rhd> Q'''' \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'''''" and "\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<sim> Q'''''" using Q'Chain bisimE(2) 
    by(metis bisimE(4) simTauChain)
  note Q''''Chain
  moreover from \<open>(\<Psi> \<otimes> \<Psi>', P, Q'') \<in> Rel\<close> \<open>\<Psi> \<otimes> \<Psi>' \<rhd> Q'' \<sim> Q'''''\<close> have "(\<Psi> \<otimes> \<Psi>', P, Q''''') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

end

context tau begin

lemma tauLaw3StatImpLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P)), \<alpha>\<cdot>Q) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P)) \<lessapprox><Rel> \<alpha>\<cdot>Q"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> \<alpha>\<cdot>Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>Q" by auto
  moreover have "insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(P)))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>Q)) \<Psi>" using insertTauAssertion
    by(nominal_induct \<alpha> rule: prefix.strong_inducts) (auto simp add: FrameStatEq_def intro: FrameStatImpTrans)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<alpha>\<cdot>Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>Q" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P)), \<alpha>\<cdot>Q) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma tauLaw3StatImpRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P, \<alpha>\<cdot>(\<tau>.(Q))) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<lessapprox><Rel> \<alpha>\<cdot>(\<tau>.(Q))"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd>  \<alpha>\<cdot>(\<tau>.(Q)) \<Longrightarrow>\<^sup>^\<^sub>\<tau>  \<alpha>\<cdot>(\<tau>.(Q))" by auto
  moreover have "insertAssertion (extractFrame(\<alpha>\<cdot>P)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(Q)))) \<Psi>" using insertTauAssertion
    by(nominal_induct \<alpha> rule: prefix.strong_inducts) (auto simp add: FrameStatEq_def intro: FrameStatImpTrans)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd>  \<alpha>\<cdot>(\<tau>.(Q)) \<Longrightarrow>\<^sup>^\<^sub>\<tau>  \<alpha>\<cdot>(\<tau>.(Q))" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P, \<alpha>\<cdot>(\<tau>.(Q))) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

end

context tauSum begin

lemma tauLaw2StatImpLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P \<oplus> \<tau>.(P), \<tau>.(P)) \<in> Rel" 

  shows "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<lessapprox><Rel> \<tau>.(P)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<tau>.(P)" by auto
  moreover have "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>" by(rule insertTauAssertion)
  hence "insertAssertion (extractFrame(P \<oplus> \<tau>.(P))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<tau>.(P))) \<Psi>" using Identity
    by(rule_tac FrameStatImpTrans) (auto simp add: FrameStatEq_def AssertionStatEq_def)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<tau>.(P)" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', P \<oplus> \<tau>.(P), \<tau>.(P)) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed  

lemma tauLaw2StatImpRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<tau>.(P), P \<oplus> \<tau>.(P)) \<in> Rel"

  shows "\<Psi> \<rhd> \<tau>.(P) \<lessapprox><Rel> P \<oplus> \<tau>.(P)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> P \<oplus> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<oplus> \<tau>.(P)" by auto
  moreover have "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>" by(rule insertTauAssertion)
  hence "insertAssertion (extractFrame(\<tau>.(P))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P \<oplus> \<tau>.(P))) \<Psi>" using Identity
    by(rule_tac FrameStatImpTrans) (auto simp add: FrameStatEq_def AssertionStatEq_def)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<oplus> \<tau>.(P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<oplus> \<tau>.(P)" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', \<tau>.(P), P \<oplus> \<tau>.(P)) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma tauLaw4StatImpLeft:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   M :: 'a
  and   N :: 'a

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<lessapprox><Rel> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
  hence "insertAssertion (extractFrame(\<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi>" 
    using insertTauAssertion Identity
    by(nominal_induct \<alpha> rule: prefix.strong_inducts, auto) 
  (rule FrameStatImpTrans[where G="\<langle>\<epsilon>, \<Psi>\<rangle>"], auto simp add: FrameStatEq_def AssertionStatEq_def)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

lemma tauLaw4StatImpRight:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<alpha> :: "'a prefix"

  assumes C1: "\<And>\<Psi>'. (\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> Rel"

  shows "\<Psi> \<rhd> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<lessapprox><Rel> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)"
proof(induct rule: weakStatImpI)
  case(cStatImp \<Psi>')
  have "\<Psi> \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
  hence "insertAssertion (extractFrame(\<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q))) \<Psi>"
    using insertTauAssertion Identity
    by(nominal_induct \<alpha> rule: prefix.strong_inducts, auto) 
  (rule FrameStatImpTrans[where G="\<langle>\<epsilon>, \<Psi>\<rangle>"], auto simp add: FrameStatEq_def AssertionStatEq_def)
  moreover have "\<Psi> \<otimes> \<Psi>' \<rhd> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q) \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)" by auto
  moreover have "(\<Psi> \<otimes> \<Psi>', \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q), \<alpha>\<cdot>P \<oplus> \<alpha>\<cdot>(\<tau>.(P) \<oplus> Q)) \<in> Rel" by(rule C1)
  ultimately show ?case by blast
qed

end

end
