(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weakening
  imports Weak_Bisimulation
begin

locale weak = env + 
  assumes weaken: "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
begin

lemma entWeaken:
  fixes \<Psi> :: 'b
  and   \<phi> :: 'c

  assumes "\<Psi> \<turnstile> \<phi>"

  shows "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>"
using assms weaken
by(auto simp add: AssertionStatImp_def)

lemma assertWeaken:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  shows "\<Psi> \<hookrightarrow> \<Psi> \<otimes> \<Psi>'"
by(auto simp add: AssertionStatImp_def entWeaken)

lemma frameWeaken:
  fixes F :: "'b frame"
  and   G :: "'b frame"

  shows "F \<hookrightarrow>\<^sub>F F \<otimes>\<^sub>F G"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* F" and  "A\<^sub>F \<sharp>* G"
    by(rule_tac F=F and C="(F, G)" in freshFrame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* F" and  "A\<^sub>G \<sharp>* G" and "A\<^sub>G \<sharp>* A\<^sub>F" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
    by(rule_tac F=G and C="(F, G, A\<^sub>F, \<Psi>\<^sub>F)" in freshFrame) auto
  from FrG \<open>A\<^sub>F \<sharp>* G\<close> \<open>A\<^sub>G \<sharp>* A\<^sub>F\<close> have "A\<^sub>F \<sharp>* \<Psi>\<^sub>G" by auto
  have "\<Psi>\<^sub>F \<hookrightarrow> \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G" by(rule weaken)
  hence "\<langle>A\<^sub>G, \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>" by(rule_tac frameImpResChainPres) auto
  with \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<close> have "\<langle>\<epsilon>, \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>G\<rangle>" using frameResFreshChain
    by(rule_tac FrameStatImpTrans) (auto simp add: FrameStatEq_def)
  with FrF FrG \<open>A\<^sub>G \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>F \<sharp>* \<Psi>\<^sub>G\<close> show ?thesis
    by(force simp add: frameChainAppend intro: frameImpResChainPres)
qed

lemma unitAssertWeaken:
  fixes \<Psi> :: 'b

  shows "\<one> \<hookrightarrow> \<Psi>"
proof -
  have "\<one> \<hookrightarrow> \<one> \<otimes> \<Psi>" by(rule assertWeaken)
  moreover have "\<one> \<otimes> \<Psi> \<hookrightarrow> \<Psi>" by(metis Identity AssertionStatEq_def Commutativity AssertionStatEqTrans)
  ultimately show ?thesis by(rule AssertionStatImpTrans)
qed

lemma unitFrameWeaken:
  fixes F :: "'b frame"

  shows "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F F"
proof -
  have "\<langle>\<epsilon>, \<one>\<rangle> \<hookrightarrow>\<^sub>F ((\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F)" by(rule frameWeaken)
  moreover obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>"
    by(rule_tac F=F and C="()" in freshFrame) auto
  hence "(\<langle>\<epsilon>, \<one>\<rangle>) \<otimes>\<^sub>F F \<simeq>\<^sub>F F" 
    by simp (metis frameIntIdentity frameIntCommutativity FrameStatEqTrans FrameStatEqSym)
  ultimately show ?thesis by(metis FrameStatImpTrans FrameStatEq_def)
qed

lemma insertAssertionWeaken:
  fixes F :: "'b frame"
  and   \<Psi> :: 'b

  shows "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F insertAssertion F \<Psi>"
proof -
  have "\<langle>\<epsilon>, \<Psi>\<rangle> \<hookrightarrow>\<^sub>F (\<langle>\<epsilon>, \<Psi>\<rangle>) \<otimes>\<^sub>F F" by(rule frameWeaken)
  thus ?thesis by simp
qed

lemma frameImpStatEq:
  fixes A\<^sub>F  :: "name list"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   \<phi>  :: 'c

  assumes "(\<langle>A\<^sub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "(\<langle>A\<^sub>F, \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>"
proof -
  obtain p::"name prm" where "(p \<bullet> A\<^sub>F) \<sharp>* \<phi>" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'"
                         and "distinctPerm p" and S: "set p \<subseteq> set A\<^sub>F \<times> set(p \<bullet> A\<^sub>F)"
    by(rule_tac c="(\<phi>, \<Psi>, \<Psi>')" in name_list_avoiding) auto
  from \<open>(\<langle>A\<^sub>F, \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<close> S have "(\<langle>(p \<bullet> A\<^sub>F), p \<bullet> \<Psi>\<rangle>) \<turnstile>\<^sub>F \<phi>" by(simp add: frameChainAlpha)
  hence "(p \<bullet> \<Psi>) \<turnstile> \<phi>" using \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<phi>\<close> by(rule frameImpE)
  moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(p \<bullet> \<Psi>) \<simeq> (p \<bullet> \<Psi>')" by(rule AssertionStatEqClosed)
  ultimately have "(p \<bullet> \<Psi>') \<turnstile> \<phi>" by(simp add: AssertionStatEq_def AssertionStatImp_def)
  hence "(\<langle>(p \<bullet> A\<^sub>F), p \<bullet> \<Psi>'\<rangle>) \<turnstile>\<^sub>F \<phi>" using \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<phi>\<close> 
    by(rule_tac frameImpI) auto
  with \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'\<close> S show ?thesis by(simp add: frameChainAlpha)
qed

lemma statImpTauDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"

  shows "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P') \<Psi>"
proof(auto simp add: FrameStatImp_def)
  fix \<phi> :: 'c
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* P" and "A\<^sub>P \<sharp>* \<phi>" and "A\<^sub>P \<sharp>* \<Psi>" and "distinct A\<^sub>P" 
    by(rule_tac C="(P, \<phi>, \<Psi>)" in freshFrame) auto
  with \<open>\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'\<close> obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" 
                                              and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* \<phi>"  and "A\<^sub>P' \<sharp>* \<Psi>" 
    by(rule_tac C="(\<Psi>, \<phi>)" in expandTauFrame) auto
  assume "insertAssertion (extractFrame P) \<Psi> \<turnstile>\<^sub>F \<phi>"
  with FrP \<open>A\<^sub>P \<sharp>* \<phi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "\<Psi> \<otimes> \<Psi>\<^sub>P \<turnstile> \<phi>" by(auto dest: frameImpE)
  hence "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  hence "\<Psi> \<otimes> \<Psi>\<^sub>P' \<turnstile> \<phi>" using \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close>
    by(rule_tac statEqEnt, auto) (metis Associativity compositionSym AssertionStatEqTrans AssertionStatEqSym Commutativity)
  with \<open>A\<^sub>P' \<sharp>* \<phi>\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<close> FrP' show "insertAssertion (extractFrame P') \<Psi> \<turnstile>\<^sub>F \<phi>"
    by(force intro: frameImpI)
qed

lemma weakenTransition:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<longmapsto> Rs"

  shows "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> Rs"
using assms
proof(nominal_induct avoiding: \<Psi>' rule: semantics.strong_induct)
  case(cInput \<Psi> M K xvec N Tvec P \<Psi>')
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case using \<open>distinct xvec\<close> \<open>set xvec \<subseteq> (supp N)\<close> \<open>length xvec = length Tvec\<close> 
    by(rule Input)
next
  case(Output \<Psi> M K N P \<Psi>')
  from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  thus ?case by(rule semantics.Output)
next
  case(Case \<Psi> P Rs \<phi> Cs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto> Rs" by(rule Case)
  moreover note \<open>(\<phi>, P) mem Cs\<close>
  moreover from \<open>\<Psi> \<turnstile> \<phi>\<close> have "\<Psi> \<otimes> \<Psi>' \<turnstile> \<phi>" by(rule entWeaken)
  ultimately show ?case using \<open>guarded P\<close>
    by(rule semantics.Case)
next
  case(cPar1 \<Psi> \<Psi>\<^sub>Q P \<alpha> P' Q A\<^sub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by(rule cPar1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  thus ?case using \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>'\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close>
    by(rule_tac Par1) auto
next
  case(cPar2 \<Psi> \<Psi>\<^sub>P Q \<alpha> Q' P A\<^sub>P \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'" by(rule cPar2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>\<alpha> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  thus ?case using \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>'\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close>
    by(rule_tac Par2) auto
next
  case(cComm1 \<Psi> \<Psi>\<^sub>Q P M N P' A\<^sub>P \<Psi>\<^sub>P Q K xvec Q' A\<^sub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'" by(rule cComm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
  moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" by(rule cComm1)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Composition Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>'\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
                              \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>'\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* P\<close>
    by(rule_tac Comm1) (assumption | auto)+
next
  case(cComm2 \<Psi> \<Psi>\<^sub>Q P M xvec N P' A\<^sub>P \<Psi>\<^sub>P Q K Q' A\<^sub>Q \<Psi>')
  have "(\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule cComm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>Q \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close>
  moreover have "(\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>' \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'" by(rule cComm2)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
    by(metis statEqTransition Composition Associativity Commutativity AssertionStatEqTrans)
  moreover note \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close>
  moreover from \<open>\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K\<close> have "(\<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>' \<turnstile> M \<leftrightarrow> K" by(rule entWeaken)
  hence "(\<Psi> \<otimes> \<Psi>') \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K" by(metis statEqEnt Composition Associativity Commutativity AssertionStatEqTrans)
  ultimately show ?case using \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>'\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* Q\<close> \<open>A\<^sub>P \<sharp>* M\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>Q\<close>
                              \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>'\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>xvec \<sharp>* Q\<close>
    by(rule_tac Comm2) (assumption | auto)+
next
  case(cOpen \<Psi> P M xvec yvec N P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'" by(rule cOpen)
  thus ?case using \<open>x \<in> supp N\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>'\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close>
    by(rule_tac Open) auto
next  
  case(cScope \<Psi> P \<alpha> P' x \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<longmapsto>\<alpha> \<prec> P'" by(rule cScope)
  thus ?case using \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<Psi>'\<close> \<open>x \<sharp> \<alpha>\<close> by(rule_tac Scope) auto
next
  case(Bang \<Psi> P Rs \<Psi>')
  have "\<Psi> \<otimes> \<Psi>' \<rhd> P \<parallel> !P\<longmapsto> Rs" by(rule Bang)
  thus ?case using \<open>guarded P\<close> by(rule semantics.Bang)
qed

end

end
