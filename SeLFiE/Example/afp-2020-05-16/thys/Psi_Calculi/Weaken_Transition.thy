(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weaken_Transition
  imports Weakening
begin

context weak
begin

definition weakenTransition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>_ \<prec> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<Longrightarrow>\<alpha> \<prec> P' \<equiv> (\<exists>P''' P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''' \<and> \<Psi> \<rhd> P''' \<longmapsto>\<alpha> \<prec> P'' \<and> \<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P') \<or> (P = P' \<and> \<alpha> = \<tau>)"

lemma weakenTransitionCases[consumes 1, case_names cBase cStep]:
  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and "Prop (\<tau>) P"
  and "\<And>P''' P''. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'''; \<Psi> \<rhd> P''' \<longmapsto>\<alpha> \<prec> P''; \<Psi> \<rhd> P'' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> Prop \<alpha> P'"

  shows "Prop \<alpha> P'"
using assms
by(auto simp add: weakenTransition_def)

lemma statImpTauChainDerivative:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  shows "insertAssertion (extractFrame P) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P') \<Psi>"
using assms
by(induct rule: tauChainInduct) (auto intro: statImpTauDerivative dest: FrameStatImpTrans)

lemma weakenTauChain:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  shows "\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms
proof(induct rule: tauChainInduct)
  case(TauBase P)
  thus ?case by simp
next
  case(TauStep P P' P'')
  note \<open>\<Psi> \<otimes> \<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'\<close>
  moreover from \<open>\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''\<close> have "\<Psi> \<otimes> \<Psi>' \<rhd> P' \<longmapsto>\<tau> \<prec> P''" by(rule weakenTransition)
  ultimately show ?case by(auto dest: tauActTauChain)
qed

end

end
