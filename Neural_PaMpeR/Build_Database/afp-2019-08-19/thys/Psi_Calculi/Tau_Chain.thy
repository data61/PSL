(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Chain
  imports Semantics
begin

context env begin

abbreviation tauChain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sup>^\<^sub>\<tau> _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'}^*"

abbreviation tauStepChain :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<Longrightarrow>\<^sub>\<tau> _" [80, 80, 80] 80)
where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<equiv> (P, P') \<in> {(P, P'). \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'}^+"

abbreviation tauContextChain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sup>^\<^sub>\<tau> _" [80, 80] 80)
where "P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
abbreviation tauContextStepChain :: "('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>\<tau> _" [80, 80] 80)
where "P \<Longrightarrow>\<^sub>\<tau> P' \<equiv> \<one> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"

lemmas tauChainInduct[consumes 1, case_names TauBase TauStep] = rtrancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'}", simplified] for \<Psi>
lemmas tauStepChainInduct[consumes 1, case_names TauBase TauStep] = trancl.induct[of _ _ "{(P, P'). \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'}", simplified] for \<Psi>


lemma tauActTauStepChain:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
using assms by auto

lemma tauActTauChain:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"

  shows "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms by(auto simp add: rtrancl_eq_or_trancl)

lemma tauStepChainEqvt[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')"
using assms
proof(induct rule: tauStepChainInduct)  
  case(TauBase P P')
  hence "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'" by simp
  thus ?case by(force dest: semantics.eqvt simp add: eqvts)
next
  case(TauStep P P' P'')
  hence "\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''" by simp  
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P') \<longmapsto>\<tau> \<prec> (p \<bullet> P'')" by(force dest: semantics.eqvt simp add: eqvts)
  with \<open>(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')\<close> show ?case
    by(subst trancl.trancl_into_trancl) auto
qed

lemma tauChainEqvt[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')"
using assms
by(auto simp add: rtrancl_eq_or_trancl eqvts)

lemma tauStepChainEqvt'[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P')) = (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')"
apply(auto simp add: eqvts perm_set_def pt_bij[OF pt_name_inst, OF at_name_inst])
by(drule_tac p="rev p" in tauStepChainEqvt) auto

lemma tauChainEqvt'[eqvt]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   p  :: "name prm"

  shows "(p \<bullet> (\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P')) = (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P')"
apply(auto simp add: eqvts perm_set_def pt_bij[OF pt_name_inst, OF at_name_inst] rtrancl_eq_or_trancl)
by(drule_tac p="rev p" in tauStepChainEqvt) auto

lemma tauStepChainFresh:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
using assms
by(induct rule: trancl.induct) (auto dest: tauFreshDerivative)

lemma tauChainFresh:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "x \<sharp> P"

  shows "x \<sharp> P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tauStepChainFresh)

lemma tauStepChainFreshChain:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tauStepChainFresh)

lemma tauChainFreshChain:
  fixes \<Psi>    :: 'b
  and   P     :: "('a, 'b, 'c) psi"
  and   P'    :: "('a, 'b, 'c) psi"
  and   xvec  :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "xvec \<sharp>* P"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: tauChainFresh)

lemma tauStepChainCase:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   \<phi>  :: 'c
  and   Cs :: "('c \<times> ('a, 'b, 'c) psi) list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "(\<phi>, P) mem Cs"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"

  shows "\<Psi> \<rhd> (Cases Cs) \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct rule: trancl.induct) (auto intro: Case trancl_into_trancl)

lemma tauStepChainResPres:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name  

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
by(induct rule: trancl.induct) (auto dest: Scope trancl_into_trancl)

lemma tauChainResPres:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   x  :: name  

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "x \<sharp> \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tauStepChainResPres)

lemma tauStepChainResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>P'"
using assms
by(induct xvec) (auto intro: tauStepChainResPres)

lemma tauChainResChainPres:
  fixes \<Psi>    :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "xvec \<sharp>* \<Psi>"

  shows "\<Psi> \<rhd> \<lparr>\<nu>*xvec\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>*xvec\<rparr>P'"
using assms
by(induct xvec) (auto intro: tauChainResPres)

lemma tauStepChainPar1:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>Q :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q"
using assms
by(induct rule: trancl.induct)  (auto dest: Par1 tauStepChainFreshChain trancl_into_trancl)

lemma tauChainPar1:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>Q :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P' \<parallel> Q"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tauStepChainPar1)

lemma tauStepChainPar2:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>P :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'"
using assms
by(induct rule: trancl.induct) (auto dest: Par2 trancl_into_trancl tauStepChainFreshChain)

lemma tauChainPar2:
  fixes \<Psi>  :: 'b
  and   \<Psi>\<^sub>P :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"

  assumes "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q'"
  and     "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<parallel> Q'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tauStepChainPar2)

lemma tauStepChainBang:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "guarded P"

  shows "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct x1=="P \<parallel> !P" P' rule: trancl.induct) (auto intro: Bang dest: Bang trancl_into_trancl)

lemma tauStepChainStatEq:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(induct rule: trancl.induct) (auto dest: statEqTransition trancl_into_trancl)

lemma tauChainStatEq:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   P'  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using assms
by(auto simp add: rtrancl_eq_or_trancl intro: tauStepChainStatEq)

definition weakTransition :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>  ('a, 'b, 'c) psi \<Rightarrow> 'a action \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ : _ \<rhd> _ \<Longrightarrow>_ \<prec> _" [80, 80, 80, 80, 80] 80)
where
  "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P' \<equiv> \<exists>P''. \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<and> (insertAssertion (extractFrame Q) \<Psi>) \<hookrightarrow>\<^sub>F (insertAssertion (extractFrame P'') \<Psi>) \<and>
                                          \<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"

lemma weakTransitionI:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   P''  :: "('a, 'b, 'c) psi"
  and   \<alpha>   :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
  and     "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
  and     "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTransition_def)

lemma weakTransitionE:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"

  obtains P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                 and "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTransition_def)

lemma weakTransitionClosed[eqvt]:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"

  assumes "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "(p \<bullet> \<Psi>) : (p \<bullet> Q) \<rhd> (p \<bullet> P) \<Longrightarrow>(p \<bullet> \<alpha>)\<prec> (p \<bullet> P')"
proof -
  from assms obtain P'' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)

  from \<open>\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sup>^\<^sub>\<tau> (p \<bullet> P'')"
    by(rule tauChainEqvt)
  moreover from \<open>insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>\<close> 
  have "(p \<bullet> (insertAssertion (extractFrame Q) \<Psi>)) \<hookrightarrow>\<^sub>F (p \<bullet> (insertAssertion (extractFrame P'') \<Psi>))"
    by(rule FrameStatImpClosed)
  hence "insertAssertion (extractFrame(p \<bullet> Q)) (p \<bullet> \<Psi>) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(p \<bullet> P'')) (p \<bullet> \<Psi>)" by(simp add: eqvts)
  moreover from \<open>\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'\<close> have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> (\<alpha> \<prec> P'))"
    by(rule semantics.eqvt)
  hence "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P'') \<longmapsto>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')" by(simp add: eqvts)
  ultimately show ?thesis by(rule weakTransitionI)
qed
(*
lemma weakTransitionAlpha:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "xvec \<sharp>* (p \<bullet> xvec)"
  and     "(p \<bullet> xvec) \<sharp>* P"
  and     "(p \<bullet> xvec) \<sharp>* N"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  note PChain QeqP''
  moreover from PChain `(p \<bullet> xvec) \<sharp>* P` have "(p \<bullet> xvec) \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans `xvec \<sharp>* (p \<bullet> xvec)` `(p \<bullet> xvec) \<sharp>* N` have "(p \<bullet> xvec) \<sharp>* P'"
    by(force intro: outputFreshChainDerivative)
  with P''Trans S `(p \<bullet> xvec) \<sharp>* N` have "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> (p \<bullet> P')"
    by(simp add: boundOutputChainAlpha'')
  ultimately show ?thesis by(rule weakTransitionI)
qed
*)
lemma weakOutputAlpha:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set xvec \<times> set(p \<bullet> xvec)"
  and     "distinctPerm p"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* (p \<bullet> xvec)"
  and     "(p \<bullet> xvec) \<sharp>* M"
  and     "distinct xvec"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(p \<bullet> xvec)\<rparr>\<langle>(p \<bullet> N)\<rangle> \<prec> P'"
    by(rule weakTransitionE)


  note PChain QeqP''
  moreover from PChain \<open>xvec \<sharp>* P\<close> have "xvec \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans \<open>xvec \<sharp>* (p \<bullet> xvec)\<close> \<open>distinct xvec\<close> \<open>(p \<bullet> xvec) \<sharp>* M\<close> have "xvec \<sharp>* (p \<bullet> N)" and "xvec \<sharp>* P'"
    by(force intro: outputFreshChainDerivative)+
  hence "(p \<bullet> xvec) \<sharp>* (p \<bullet> p \<bullet> N)" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')"
    by(simp add: pt_fresh_star_bij[OF pt_name_inst, OF at_name_inst])+
  with \<open>distinctPerm p\<close> have "(p \<bullet> xvec) \<sharp>* N" and "(p \<bullet> xvec) \<sharp>* (p \<bullet> P')" by simp+
  with P''Trans S \<open>distinctPerm p\<close> have "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> (p \<bullet> P')"
    apply(simp add: residualInject)
    by(subst boundOutputChainAlpha) auto
    
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakFreshDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> \<alpha>"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"

  shows "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>x \<sharp> P\<close> have "x \<sharp> P''" by(rule tauChainFresh)
  with P''Trans show "x \<sharp> P'" using \<open>x \<sharp> \<alpha>\<close> \<open>bn \<alpha> \<sharp>* subject \<alpha>\<close> \<open>distinct(bn \<alpha>)\<close>
    by(force intro: freeFreshDerivative)
qed

lemma weakFreshChainDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "yvec \<sharp>* P"
  and     "yvec \<sharp>* \<alpha>"
  and     "bn \<alpha> \<sharp>* subject \<alpha>"
  and     "distinct(bn \<alpha>)"

  shows "yvec \<sharp>* P'"
using assms
by(induct yvec) (auto intro: weakFreshDerivative)

lemma weakInputFreshDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> N"

  shows "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>x \<sharp> P\<close> have "x \<sharp> P''" by(rule tauChainFresh)
  with P''Trans show "x \<sharp> P'" using \<open>x \<sharp> N\<close> 
    by(force intro: inputFreshDerivative)
qed

lemma weakInputFreshChainDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   xvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     "xvec \<sharp>* P"
  and     "xvec \<sharp>* N"

  shows "xvec \<sharp>* P'"
using assms
by(induct xvec) (auto intro: weakInputFreshDerivative)

lemma weakOutputFreshDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   x    :: name

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<sharp> P"
  and     "x \<sharp> xvec"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"

  shows "x \<sharp> N"
  and   "x \<sharp> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>x \<sharp> P\<close> have "x \<sharp> P''" by(rule tauChainFresh)
  with P''Trans show "x \<sharp> N" and "x \<sharp> P'" using \<open>x \<sharp> xvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
    by(force intro: outputFreshDerivative)+
qed

lemma weakOutputFreshChainDerivative:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   yvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "yvec \<sharp>* P"
  and     "xvec \<sharp>* yvec"
  and     "xvec \<sharp>* M"
  and     "distinct xvec"

  shows "yvec \<sharp>* N"
  and   "yvec \<sharp>* P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>yvec \<sharp>* P\<close> have "yvec \<sharp>* P''" by(rule tauChainFreshChain)
  with P''Trans show "yvec \<sharp>* N" and "yvec \<sharp>* P'" using \<open>xvec \<sharp>* yvec\<close> \<open>xvec \<sharp>* M\<close> \<open>distinct xvec\<close>
    by(force intro: outputFreshChainDerivative)+
qed

lemma weakOutputPermSubject:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>yvec \<sharp>* P\<close> \<open>zvec \<sharp>* P\<close> have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tauChainFreshChain)+

  note PChain QeqP''
  moreover from P''Trans S \<open>yvec \<sharp>* \<Psi>\<close> \<open>zvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P''\<close> \<open>zvec \<sharp>* P''\<close> have "\<Psi> \<rhd> P'' \<longmapsto>(p \<bullet> M)\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule_tac outputPermSubject) (assumption | auto)
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakInputPermSubject:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   p    :: "name prm"
  and   yvec :: "name list"
  and   zvec :: "name list"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     S: "set p \<subseteq> set yvec \<times> set zvec"
  and     "yvec \<sharp>* \<Psi>"
  and     "zvec \<sharp>* \<Psi>"
  and     "yvec \<sharp>* P"
  and     "zvec \<sharp>* P"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>" 
                            and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>yvec \<sharp>* P\<close> \<open>zvec \<sharp>* P\<close> have "yvec \<sharp>* P''" and "zvec \<sharp>* P''"
    by(force intro: tauChainFreshChain)+

  note PChain QeqP''
  moreover from P''Trans S \<open>yvec \<sharp>* \<Psi>\<close> \<open>zvec \<sharp>* \<Psi>\<close> \<open>yvec \<sharp>* P''\<close> \<open>zvec \<sharp>* P''\<close> have "\<Psi> \<rhd> P'' \<longmapsto>(p \<bullet> M)\<lparr>N\<rparr> \<prec> P'"
    by(rule_tac inputPermSubject) auto
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakInput:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Tvec :: "'a list"
  and   P    :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     "distinct xvec" 
  and     "set xvec \<subseteq> supp N"
  and     "length xvec = length Tvec"
  and     Qeq\<Psi>: "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
proof -
  have "\<Psi> \<rhd>  M\<lparr>\<lambda>*xvec N\<rparr>.P \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<lparr>\<lambda>*xvec N\<rparr>.P" by simp
  moreover from Qeq\<Psi> have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<lparr>\<lambda>*xvec N\<rparr>.P)) \<Psi>"
    by auto
  moreover from assms have "\<Psi> \<rhd> M\<lparr>\<lambda>*xvec N\<rparr>.P \<longmapsto>K\<lparr>(N[xvec::=Tvec])\<rparr> \<prec> P[xvec::=Tvec]"
    by(rule_tac Input)
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakOutput:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   K    :: 'a
  and   N    :: 'a
  and   P    :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<turnstile> M \<leftrightarrow> K"
  and     Qeq\<Psi>: "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"

  shows "\<Psi> : Q \<rhd> M\<langle>N\<rangle>.P \<Longrightarrow>K\<langle>N\<rangle> \<prec> P"
proof -
  have "\<Psi> \<rhd>  M\<langle>N\<rangle>.P \<Longrightarrow>\<^sup>^\<^sub>\<tau> M\<langle>N\<rangle>.P" by simp
  moreover from Qeq\<Psi> have "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi>"
    by auto
  moreover have "insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(M\<langle>N\<rangle>.P)) \<Psi>" by simp
  moreover from \<open>\<Psi> \<turnstile> M \<leftrightarrow> K\<close> have "\<Psi> \<rhd> M\<langle>N\<rangle>.P \<longmapsto>K\<langle>N\<rangle> \<prec> P"
    by(rule Output)
  ultimately show ?thesis by(rule_tac weakTransitionI) auto
qed

lemma insertGuardedAssertion:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
  from \<open>guarded P\<close> FrP have "\<Psi>\<^sub>P \<simeq> \<one>" and "supp \<Psi>\<^sub>P = ({}::name set)"
    by(blast dest: guardedStatEq)+
  
  from FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "insertAssertion(extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
    by simp (metis frameIntCompositionSym)
  moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
    by(rule_tac frameResFreshChain) auto
  ultimately show ?thesis by(rule FrameStatEqTrans)
qed
  
lemma weakCase:
  fixes \<Psi>   :: 'b 
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "(\<phi>, P) mem CsP"
  and     "\<Psi> \<turnstile> \<phi>"
  and     "guarded P"
  and     RImpQ: "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and     ImpR: "insertAssertion (extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"

  shows "\<Psi> : R \<rhd> Cases CsP \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)
  show ?thesis
  proof(case_tac "P = P''")
    assume "P = P''"
    have "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sup>^\<^sub>\<tau> Cases CsP" by simp
    moreover from ImpR AssertionStatEq_def have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(Cases CsP)) \<Psi>"
      by(rule_tac FrameStatImpTrans) (auto intro: Identity)+

    moreover from P''Trans \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> \<open>P = P''\<close> have "\<Psi> \<rhd> Cases CsP \<longmapsto>\<alpha> \<prec> P'"
      by(blast intro: Case)
    ultimately show ?thesis
      by(rule weakTransitionI)
  next
    assume "P \<noteq> P''"
    with PChain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by(simp add: rtrancl_eq_or_trancl)
    hence "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sub>\<tau> P''" using \<open>(\<phi>, P) mem CsP\<close> \<open>\<Psi> \<turnstile> \<phi>\<close> \<open>guarded P\<close> 
      by(rule tauStepChainCase)
    hence "\<Psi> \<rhd> Cases CsP \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    moreover from RImpQ QeqP'' have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
      by(rule FrameStatImpTrans)
    ultimately show ?thesis using P''Trans by(rule weakTransitionI)
  qed
qed

lemma weakOpen:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   yvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "x \<in> supp N"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> M"
  and     "x \<sharp> xvec"
  and     "x \<sharp> yvec"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*(xvec@yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>x \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tauChainResPres)
  moreover from QeqP'' \<open>x \<sharp> \<Psi>\<close> have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frameImpResPres)
  moreover from P''Trans \<open>x \<in> supp N\<close> \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> M\<close> \<open>x \<sharp> xvec\<close> \<open>x \<sharp> yvec\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>M\<lparr>\<nu>*(xvec@x#yvec)\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule Open)
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakScope:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "x \<sharp> \<Psi>"
  and     "x \<sharp> \<alpha>"

  shows "\<Psi> : \<lparr>\<nu>x\<rparr>Q \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>x \<sharp> \<Psi>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P''" by(rule tauChainResPres)
  moreover from QeqP'' \<open>x \<sharp> \<Psi>\<close> have "insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(\<lparr>\<nu>x\<rparr>P'')) \<Psi>" by(force intro: frameImpResPres)
  moreover from P''Trans \<open>x \<sharp> \<Psi>\<close> \<open>x \<sharp> \<alpha>\<close> have "\<Psi> \<rhd> \<lparr>\<nu>x\<rparr>P'' \<longmapsto>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
    by(rule Scope)
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakPar1:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     "bn \<alpha> \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* \<alpha>"
  and     "A\<^sub>Q \<sharp>* R"

  shows "\<Psi> : R \<parallel> Q \<rhd> P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> P' \<parallel> Q"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and ReqP'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>A\<^sub>Q \<sharp>* P\<close> have "A\<^sub>Q \<sharp>* P''" by(rule tauChainFreshChain)
  from PChain FrQ \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tauChainPar1)
  moreover have "insertAssertion (extractFrame(R \<parallel> Q)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P'' \<parallel> Q)) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>Q, \<Psi>\<^sub>Q, \<Psi>)" in freshFrame) auto

    from FrR FrP'' \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* P''\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q\<close> have "A\<^sub>Q \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    moreover from ReqP'' FrR FrP'' \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q\<close>
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using freshCompChain by auto
    moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)

    hence "\<langle>(A\<^sub>R@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P''@A\<^sub>Q), \<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>Q in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrQ FrP'' \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<^sub>P''\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> ReqP''
    show ?thesis by simp
  qed
  moreover from P''Trans FrQ \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P''\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>\<alpha> \<prec> (P' \<parallel> Q)"
    by(rule Par1)  
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakPar2:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   Q'   :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   A\<^sub>P   :: "name list"
  and   \<Psi>\<^sub>P  :: 'b

  assumes QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>P : R \<rhd> Q \<Longrightarrow>\<alpha> \<prec> Q'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "bn \<alpha> \<sharp>* P"
  and     "A\<^sub>P \<sharp>* \<Psi>"
  and     "A\<^sub>P \<sharp>* Q"
  and     "A\<^sub>P \<sharp>* \<alpha>"
  and     "A\<^sub>P \<sharp>* R"

  shows "\<Psi> : P \<parallel> R \<rhd> P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> P \<parallel> Q'"
proof -
  from QTrans obtain Q'' where QChain: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> Q''"
                           and ReqQ'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>P) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame Q'') (\<Psi> \<otimes> \<Psi>\<^sub>P)"
                           and Q''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>P \<rhd> Q'' \<longmapsto>\<alpha> \<prec> Q'"
    by(rule weakTransitionE)

  from QChain \<open>A\<^sub>P \<sharp>* Q\<close> have "A\<^sub>P \<sharp>* Q''" by(rule tauChainFreshChain)

  from QChain FrP \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q\<close> have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P \<parallel> Q''" by(rule tauChainPar2)
  moreover have "insertAssertion (extractFrame(P \<parallel> R)) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame(P \<parallel> Q'')) \<Psi>"
  proof -
    obtain A\<^sub>R \<Psi>\<^sub>R where FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>" and "A\<^sub>R \<sharp>* A\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>R \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto
    obtain A\<^sub>Q'' \<Psi>\<^sub>Q'' where FrQ'': "extractFrame Q'' = \<langle>A\<^sub>Q'', \<Psi>\<^sub>Q''\<rangle>" and "A\<^sub>Q'' \<sharp>* A\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>Q'' \<sharp>* \<Psi>"
      by(rule_tac C="(A\<^sub>P, \<Psi>\<^sub>P, \<Psi>)" in freshFrame) auto

    from FrR FrQ'' \<open>A\<^sub>P \<sharp>* R\<close> \<open>A\<^sub>P \<sharp>* Q''\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q'' \<sharp>* A\<^sub>P\<close> have "A\<^sub>P \<sharp>* \<Psi>\<^sub>R" and "A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''"
      by(force dest: extractFrameFreshChain)+
    have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)

    moreover from ReqQ'' FrR FrQ'' \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>Q'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P\<close>
    have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle>" using freshCompChain by simp
    moreover have "\<langle>A\<^sub>Q'', (\<Psi> \<otimes> \<Psi>\<^sub>P) \<otimes> \<Psi>\<^sub>Q''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(metis frameNilStatEq frameResChainPres Associativity Commutativity Composition AssertionStatEqTrans)
    ultimately have "\<langle>A\<^sub>R, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>Q'', \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      by(force dest: FrameStatImpTrans simp add: FrameStatEq_def)
    hence "\<langle>(A\<^sub>P@A\<^sub>R), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>(A\<^sub>P@A\<^sub>Q''), \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<Psi>\<^sub>Q''\<rangle>"
      apply(simp add: frameChainAppend)
      apply(drule_tac xvec=A\<^sub>P in frameImpResChainPres)
      by(metis frameImpChainComm FrameStatImpTrans)
    with FrR FrP FrQ'' \<open>A\<^sub>R \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>R\<close> \<open>A\<^sub>Q'' \<sharp>* A\<^sub>P\<close> \<open>A\<^sub>Q'' \<sharp>* \<Psi>\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>Q''\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> ReqQ''
    show ?thesis by simp
  qed
  moreover from Q''Trans FrP \<open>bn \<alpha> \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>P \<sharp>* Q''\<close> \<open>A\<^sub>P \<sharp>* \<alpha>\<close> have "\<Psi> \<rhd> P \<parallel> Q'' \<longmapsto>\<alpha> \<prec> (P \<parallel> Q')"
    by(rule_tac Par2) auto
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma weakComm1:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>N\<rparr> \<prec> P'"
  and     FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* M"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* K"
  and     "xvec \<sharp>* P"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
proof -
  from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>Q' where FrQ': "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" 
               and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K" and "A\<^sub>R \<sharp>* A\<^sub>Q'"
    by(rule_tac C="(\<Psi>, P, Q, R, K, A\<^sub>R)" in distinctFrame) auto

  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and RimpP'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>A\<^sub>Q' \<sharp>* P\<close> have "A\<^sub>Q' \<sharp>* P''" by(rule tauChainFreshChain)
  obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* (\<Psi>, A\<^sub>Q', \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, Q, P'', xvec)" and "distinct A\<^sub>P''"
    by(rule freshFrame)
  hence "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q'" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* Q"
    and "A\<^sub>P'' \<sharp>* N" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R"
    by simp+
  from FrR \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" by(drule_tac extractFrameFreshChain) auto
  from FrQ' \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extractFrameFreshChain) auto
  from PChain \<open>xvec \<sharp>* P\<close> have "xvec \<sharp>* P''" by(force intro: tauChainFreshChain)+

  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" 
    by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
  moreover with RimpP'' FrP'' FrR \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close>
  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using freshCompChain
    by(simp add: freshChainSimps)
  moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
  ultimately have RImpP'': "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule FrameStatEqImpCompose)
      
  from PChain FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tauChainPar1)
  moreover from QTrans FrR P''Trans MeqK RImpP'' FrP'' FrQ' \<open>distinct A\<^sub>P''\<close> \<open>distinct A\<^sub>Q'\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close>
        \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P''\<close> \<open>A\<^sub>Q' \<sharp>* Q\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> \<open>A\<^sub>Q' \<sharp>* K\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close> \<open>A\<^sub>P'' \<sharp>* Q\<close>
        \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* M\<close>
  obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> Q \<longmapsto>K'\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> Q'" and "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>Q' \<sharp>* K'"
    by(rule_tac comm1Aux) (assumption | simp)+
  with P''Trans FrP'' have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')" using FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P''\<close> \<open>A\<^sub>Q' \<sharp>* Q\<close>
    \<open>xvec \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* Q\<close> \<open>A\<^sub>P'' \<sharp>* M\<close>  \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q'\<close>
    by(rule_tac Comm1)
  ultimately show ?thesis
    by(drule_tac tauActTauStepChain) auto
qed

lemma weakComm2:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"
  and   A\<^sub>Q   :: "name list"
  and   \<Psi>\<^sub>Q   :: 'b

  assumes PTrans: "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     FrR: "extractFrame R = \<langle>A\<^sub>R, \<Psi>\<^sub>R\<rangle>"
  and     QTrans: "\<Psi> \<otimes> \<Psi>\<^sub>R \<rhd> Q \<longmapsto>K\<lparr>N\<rparr> \<prec> Q'"
  and     FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>"
  and     MeqK: "\<Psi> \<otimes> \<Psi>\<^sub>R \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K"
  and     "A\<^sub>R \<sharp>* \<Psi>"
  and     "A\<^sub>R \<sharp>* P"
  and     "A\<^sub>R \<sharp>* Q"
  and     "A\<^sub>R \<sharp>* R"
  and     "A\<^sub>R \<sharp>* M"
  and     "A\<^sub>R \<sharp>* A\<^sub>Q"
  and     "A\<^sub>Q \<sharp>* \<Psi>"
  and     "A\<^sub>Q \<sharp>* P"
  and     "A\<^sub>Q \<sharp>* Q"
  and     "A\<^sub>Q \<sharp>* R"
  and     "A\<^sub>Q \<sharp>* K"
  and     "xvec \<sharp>* Q"
  and     "xvec \<sharp>* M"
  and     "xvec \<sharp>* A\<^sub>Q"
  and     "xvec \<sharp>* A\<^sub>R"

  shows "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> (\<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q'))"
proof -
  from \<open>extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>Q \<sharp>* K\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q\<close> \<open>xvec \<sharp>* A\<^sub>Q\<close>
  obtain A\<^sub>Q' where FrQ': "extractFrame Q = \<langle>A\<^sub>Q', \<Psi>\<^sub>Q\<rangle>" and "distinct A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* \<Psi>" and "A\<^sub>Q' \<sharp>* P" 
               and "A\<^sub>Q' \<sharp>* Q" and "A\<^sub>Q' \<sharp>* R" and "A\<^sub>Q' \<sharp>* K" and "A\<^sub>R \<sharp>* A\<^sub>Q'" and "A\<^sub>Q' \<sharp>* xvec"
    by(rule_tac C="(\<Psi>, P, Q, R, K, A\<^sub>R, xvec)" in distinctFrame) auto

  from PTrans obtain P'' where PChain: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and RimpP'': "insertAssertion (extractFrame R) (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') (\<Psi> \<otimes> \<Psi>\<^sub>Q)"
                           and P''Trans: "\<Psi> \<otimes> \<Psi>\<^sub>Q \<rhd> P'' \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>A\<^sub>Q' \<sharp>* P\<close> have "A\<^sub>Q' \<sharp>* P''" by(rule tauChainFreshChain)
  obtain A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "A\<^sub>P'' \<sharp>* (\<Psi>, A\<^sub>Q', \<Psi>\<^sub>Q, A\<^sub>R, \<Psi>\<^sub>R, M, N, K, R, Q, P'', xvec)" and "distinct A\<^sub>P''"
    by(rule freshFrame)
  hence "A\<^sub>P'' \<sharp>* \<Psi>" and "A\<^sub>P'' \<sharp>* A\<^sub>Q'" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q" and "A\<^sub>P'' \<sharp>* M" and "A\<^sub>P'' \<sharp>* R" and "A\<^sub>P'' \<sharp>* Q"
    and "A\<^sub>P'' \<sharp>* N" and "A\<^sub>P'' \<sharp>* K" and "A\<^sub>P'' \<sharp>* A\<^sub>R" and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* xvec" and "A\<^sub>P'' \<sharp>* \<Psi>\<^sub>R"
    by simp+
  from FrR \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> have "A\<^sub>Q' \<sharp>* \<Psi>\<^sub>R" by(drule_tac extractFrameFreshChain) auto
  from FrQ' \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>R \<sharp>* Q\<close> have "A\<^sub>R \<sharp>* \<Psi>\<^sub>Q" by(drule_tac extractFrameFreshChain) auto

  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle>" 
    by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
  moreover with RimpP'' FrP'' FrR \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<^sub>Q\<close> \<open>A\<^sub>R \<sharp>* \<Psi>\<^sub>Q\<close>
  have "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>R\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle>" using freshCompChain
    by(simp add: freshChainSimps)
  moreover have "\<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>Q) \<otimes> \<Psi>\<^sub>P''\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(metis frameResChainPres frameNilStatEq Commutativity AssertionStatEqTrans Composition Associativity)
  ultimately have RImpP'': "\<langle>A\<^sub>R, (\<Psi> \<otimes> \<Psi>\<^sub>R) \<otimes> \<Psi>\<^sub>Q\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P'', (\<Psi> \<otimes> \<Psi>\<^sub>P'') \<otimes> \<Psi>\<^sub>Q\<rangle>"
    by(rule FrameStatEqImpCompose)
      
  from PChain FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P\<close> have "\<Psi> \<rhd> P \<parallel> Q \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'' \<parallel> Q" by(rule tauChainPar1)
  moreover from QTrans FrR P''Trans MeqK RImpP'' FrP'' FrQ' \<open>distinct A\<^sub>P''\<close> \<open>distinct A\<^sub>Q'\<close> \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q'\<close> \<open>A\<^sub>R \<sharp>* A\<^sub>Q'\<close>
        \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P''\<close> \<open>A\<^sub>Q' \<sharp>* Q\<close> \<open>A\<^sub>Q' \<sharp>* R\<close> \<open>A\<^sub>Q' \<sharp>* K\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* R\<close> \<open>A\<^sub>P'' \<sharp>* Q\<close>
        \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* M\<close> \<open>A\<^sub>Q \<sharp>* R\<close> \<open>A\<^sub>R \<sharp>* Q\<close> \<open>A\<^sub>R \<sharp>* M\<close> \<open>xvec \<sharp>* A\<^sub>R\<close> \<open>xvec \<sharp>* M\<close> \<open>A\<^sub>Q' \<sharp>* xvec\<close>
  obtain K' where "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<rhd> Q \<longmapsto>K'\<lparr>N\<rparr> \<prec> Q'" and "\<Psi> \<otimes> \<Psi>\<^sub>P'' \<otimes> \<Psi>\<^sub>Q \<turnstile> M \<leftrightarrow> K'" and "A\<^sub>Q' \<sharp>* K'"
    by(rule_tac comm2Aux) (assumption | simp)+
  with P''Trans FrP'' have "\<Psi> \<rhd> P'' \<parallel> Q \<longmapsto>\<tau> \<prec> \<lparr>\<nu>*xvec\<rparr>(P' \<parallel> Q')" using FrQ' \<open>A\<^sub>Q' \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q' \<sharp>* P''\<close> \<open>A\<^sub>Q' \<sharp>* Q\<close>
    \<open>xvec \<sharp>* Q\<close> \<open>A\<^sub>P'' \<sharp>* \<Psi>\<close> \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* Q\<close> \<open>A\<^sub>P'' \<sharp>* M\<close>  \<open>A\<^sub>P'' \<sharp>* A\<^sub>Q'\<close>
    by(rule_tac Comm2)
  ultimately show ?thesis
    by(drule_tac tauActTauStepChain) auto
qed

lemma frameImpIntComposition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
proof -
  from assms have "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>" by(rule frameIntComposition)
  thus ?thesis by(simp add: FrameStatEq_def)
qed

lemma insertAssertionStatImp:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes FeqG: "insertAssertion F \<Psi> \<hookrightarrow>\<^sub>F insertAssertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insertAssertion F \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto

  from \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle>" by (metis frameIntComposition FrameStatEqSym)
  moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<langle>A\<^sub>G, \<Psi> \<otimes> \<Psi>\<^sub>G\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" by(rule frameIntComposition)
  ultimately have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>" using FeqG FrF FrG \<open>A\<^sub>F \<sharp>* \<Psi>\<close> \<open>A\<^sub>G \<sharp>* \<Psi>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
    by(force simp add: FrameStatEq_def dest: FrameStatImpTrans)
  with FrF FrG \<open>A\<^sub>F \<sharp>* \<Psi>'\<close> \<open>A\<^sub>G \<sharp>* \<Psi>'\<close> show ?thesis by simp
qed

lemma insertAssertionStatEq:
  fixes F  :: "'b frame"
  and   \<Psi>  :: 'b
  and   G  :: "'b frame"
  and   \<Psi>' :: 'b

  assumes FeqG: "insertAssertion F \<Psi> \<simeq>\<^sub>F insertAssertion G \<Psi>"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "insertAssertion F \<Psi>' \<simeq>\<^sub>F insertAssertion G \<Psi>'"
proof -
  obtain A\<^sub>F \<Psi>\<^sub>F where FrF: "F = \<langle>A\<^sub>F, \<Psi>\<^sub>F\<rangle>" and "A\<^sub>F \<sharp>* \<Psi>" and "A\<^sub>F \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
  obtain A\<^sub>G \<Psi>\<^sub>G where FrG: "G = \<langle>A\<^sub>G, \<Psi>\<^sub>G\<rangle>" and "A\<^sub>G \<sharp>* \<Psi>" and "A\<^sub>G \<sharp>* \<Psi>'"
    by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto

  from FeqG FrF FrG \<open>A\<^sub>F \<sharp>* \<Psi>\<close> \<open>A\<^sub>G \<sharp>* \<Psi>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
  have "\<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>G, \<Psi>' \<otimes> \<Psi>\<^sub>G\<rangle>"
    by simp (metis frameIntComposition FrameStatEqTrans FrameStatEqSym)
  with FrF FrG \<open>A\<^sub>F \<sharp>* \<Psi>'\<close> \<open>A\<^sub>G \<sharp>* \<Psi>'\<close> show ?thesis by simp
qed

lemma weakTransitionStatEq:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and QeqP'': "insertAssertion (extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)

  from PChain \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by(rule tauChainStatEq)
  moreover from QeqP'' \<open>\<Psi> \<simeq> \<Psi>'\<close> have "insertAssertion (extractFrame Q) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (extractFrame P'') \<Psi>'"
    by(rule insertAssertionStatImp)
  moreover from P''Trans \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule statEqTransition)
  ultimately show ?thesis by(rule weakTransitionI)
qed

lemma transitionWeakTransition:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>\<alpha> \<prec> P'"
  and     "insertAssertion(extractFrame Q) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P) \<Psi>"

  shows "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(fastforce intro: weakTransitionI)

lemma weakPar1Guarded:
  fixes \<Psi>  :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "bn \<alpha> \<sharp>* Q"
  and     "guarded Q"

  shows "\<Psi> : (R \<parallel> Q) \<rhd> P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> P' \<parallel> Q"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* P" and "A\<^sub>Q \<sharp>* \<alpha>" and "A\<^sub>Q \<sharp>* R"
    by(rule_tac C="(\<Psi>, P, \<alpha>, R)" in freshFrame) auto
  from \<open>guarded Q\<close> FrQ have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guardedStatEq)
  with PTrans have "\<Psi> \<otimes> \<Psi>\<^sub>Q : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'" by(metis weakTransitionStatEq Identity AssertionStatEqSym compositionSym)
  thus ?thesis using FrQ \<open>bn \<alpha> \<sharp>* Q\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* P\<close> \<open>A\<^sub>Q \<sharp>* \<alpha>\<close> \<open>A\<^sub>Q \<sharp>* R\<close> 
    by(rule weakPar1)
qed

lemma weakBang:
  fixes \<Psi>   :: 'b
  and   R    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   Q    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : R \<rhd> P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "guarded P"

  shows "\<Psi> : R \<rhd> !P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  from PTrans obtain P'' where PChain: "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''"
                           and RImpP'': "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
                           and P''Trans: "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    by(rule weakTransitionE)
  moreover obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" by(rule freshFrame)
  moreover from \<open>guarded P\<close> FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guardedStatEq)
  ultimately show ?thesis
  proof(auto simp add: rtrancl_eq_or_trancl)
    have "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> !P" by simp
    moreover assume RimpP: "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle>"
    have "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame(!P)) \<Psi>"
    proof -
      from \<open>\<Psi>\<^sub>P \<simeq> \<one>\<close> have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<Psi>\<^sub>P \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle>"
        by(metis frameIntCompositionSym frameIntAssociativity frameIntCommutativity frameIntIdentity FrameStatEqTrans FrameStatEqSym)
      moreover from \<open>A\<^sub>P \<sharp>* \<Psi>\<close> have "\<langle>A\<^sub>P, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>"
        by(force intro: frameResFreshChain)
      ultimately show ?thesis using RimpP by(auto simp add: FrameStatEq_def dest: FrameStatImpTrans)
    qed
    moreover assume "\<Psi> \<rhd> P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'"
    hence "\<Psi> \<rhd> !P \<longmapsto>\<alpha> \<prec> P'" using \<open>guarded P\<close> by(rule Bang)
   ultimately show ?thesis by(rule weakTransitionI)
  next
    fix P'''
    assume "\<Psi> \<rhd> P \<parallel> !P \<Longrightarrow>\<^sub>\<tau>  P''"
    hence "\<Psi> \<rhd> !P \<Longrightarrow>\<^sub>\<tau> P''" using \<open>guarded P\<close> by(rule tauStepChainBang)
    hence "\<Psi> \<rhd> !P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" by simp
    moreover assume "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame P'') \<Psi>"
                and "\<Psi> \<rhd> P'' \<longmapsto>\<alpha> \<prec> P'"
    ultimately show ?thesis by(rule weakTransitionI)
  qed
qed

lemma weakTransitionFrameImp:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and             "insertAssertion(extractFrame R) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion(extractFrame Q) \<Psi>"

  shows "\<Psi> : R \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTransition_def intro: FrameStatImpTrans)

lemma guardedFrameStatEq:
  fixes P :: "('a, 'b, 'c) psi"

  assumes "guarded P"

  shows "extractFrame P \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>"
proof -
  obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by(rule freshFrame)
  from \<open>guarded P\<close> FrP have "\<Psi>\<^sub>P \<simeq> \<one>" by(blast dest: guardedStatEq)
  hence "\<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>P, \<one>\<rangle>" by(rule_tac frameResChainPres) auto
  moreover have "\<langle>A\<^sub>P, \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<one>\<rangle>" by(rule_tac frameResFreshChain) auto
  ultimately show ?thesis using FrP by(force intro: FrameStatEqTrans)
qed

lemma weakGuardedTransition:
  fixes \<Psi>   :: 'b
  and   Q    :: "('a, 'b, 'c) psi"
  and   P    :: "('a, 'b, 'c) psi"
  and   \<alpha>    :: "'a action"
  and   P'   :: "('a, 'b, 'c) psi"
  and   R    :: "('a, 'b, 'c) psi"

  assumes PTrans: "\<Psi> : Q \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
  and    "guarded Q"

  shows "\<Psi> : \<zero> \<rhd> P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" by(rule freshFrame)
  moreover from \<open>guarded Q\<close> FrQ have "\<Psi>\<^sub>Q \<simeq> \<one>" by(blast dest: guardedStatEq)
  hence "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<Psi>\<^sub>Q\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle>" by(metis frameIntCompositionSym)
  moreover from \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> have "\<langle>A\<^sub>Q, \<Psi> \<otimes> \<one>\<rangle> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi> \<otimes> \<one>\<rangle>" by(rule_tac frameResFreshChain) auto
  ultimately have "insertAssertion(extractFrame Q) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame (\<zero>)) \<Psi>"
    using FrQ \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> by simp (blast intro: FrameStatEqTrans)
  with PTrans show ?thesis by(rule_tac weakTransitionFrameImp) (auto simp add: FrameStatEq_def) 
qed

lemma expandTauChainFrame:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   C   :: "'d::fs_name"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     "A\<^sub>P \<sharp>* P"
  and     "A\<^sub>P \<sharp>* C"

  obtains \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'" and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
using PChain FrP \<open>A\<^sub>P \<sharp>* P\<close>
proof(induct arbitrary: thesis rule: tauChainInduct)
  case(TauBase P)
  have "\<Psi>\<^sub>P \<otimes> SBottom' \<simeq> \<Psi>\<^sub>P" by(rule Identity)
  with \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> show ?case using \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* C\<close> \<open>distinct A\<^sub>P\<close> by(rule TauBase)
next
  case(TauStep P P' P'')
  from \<open>extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>\<close> \<open>A\<^sub>P \<sharp>* P\<close>
  obtain \<Psi>' A\<^sub>P' \<Psi>\<^sub>P' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                       and "A\<^sub>P' \<sharp>* P'" and "A\<^sub>P' \<sharp>* C" and "distinct A\<^sub>P'"
    by(rule_tac TauStep)
  from \<open>\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''\<close> FrP' \<open>distinct A\<^sub>P'\<close> \<open>A\<^sub>P' \<sharp>* P'\<close> \<open>A\<^sub>P' \<sharp>* C\<close>
  obtain \<Psi>'' A\<^sub>P'' \<Psi>\<^sub>P'' where FrP'': "extractFrame P'' = \<langle>A\<^sub>P'', \<Psi>\<^sub>P''\<rangle>" and "\<Psi>\<^sub>P' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''"
                          and "A\<^sub>P'' \<sharp>* P''" and "A\<^sub>P'' \<sharp>* C" and "distinct A\<^sub>P''"
    by(rule expandTauFrame)
  from \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close> have "(\<Psi>\<^sub>P \<otimes> \<Psi>') \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P' \<otimes> \<Psi>''" by(rule Composition)
  with \<open>\<Psi>\<^sub>P' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''\<close> have "\<Psi>\<^sub>P \<otimes> \<Psi>' \<otimes> \<Psi>'' \<simeq> \<Psi>\<^sub>P''"
    by(metis AssertionStatEqTrans Associativity Commutativity)
  with FrP'' show ?case using \<open>A\<^sub>P'' \<sharp>* P''\<close> \<open>A\<^sub>P'' \<sharp>* C\<close> \<open>distinct A\<^sub>P''\<close>
    by(rule TauStep)
qed

lemma frameIntImpComposition:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b
  and   A\<^sub>F :: "name list"
  and   \<Psi>\<^sub>F :: 'b

  assumes "\<Psi> \<simeq> \<Psi>'"

  shows "\<langle>A\<^sub>F, \<Psi> \<otimes> \<Psi>\<^sub>F\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>F, \<Psi>' \<otimes> \<Psi>\<^sub>F\<rangle>"
using assms frameIntComposition
by(simp add: FrameStatEq_def)

lemma tauChainInduct2[consumes 1, case_names TauBase TauStep]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     cBase: "\<And>P. Prop P P"
  and     cStep: "\<And>P P' P''. \<lbrakk>\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''; \<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'; Prop P P'\<rbrakk> \<Longrightarrow> Prop P P''"

  shows "Prop P P'"
using assms
by(rule tauChainInduct)

lemma tauStepChainInduct2[consumes 1, case_names TauBase TauStep]:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'"
  and     cBase: "\<And>P P'. \<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> Prop P P'"
  and     cStep: "\<And>P P' P''. \<lbrakk>\<Psi> \<rhd> P' \<longmapsto>\<tau> \<prec> P''; \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'; Prop P P'\<rbrakk> \<Longrightarrow> Prop P P''"

  shows "Prop P P'"
using assms
by(rule tauStepChainInduct)

lemma weakTransferTauChainFrame:
  fixes \<Psi>\<^sub>F :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  and   A\<^sub>P :: "name list"
  and   \<Psi>\<^sub>P :: 'b
  and   A\<^sub>F :: "name list"
  and   A\<^sub>G :: "name list"
  and   \<Psi>\<^sub>G :: 'b

  assumes PChain: "\<Psi>\<^sub>F \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>"
  and     "distinct A\<^sub>P"
  and     FeqG: "\<And>\<Psi>. insertAssertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi> \<hookrightarrow>\<^sub>F insertAssertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>"
  and     "A\<^sub>F \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>G \<sharp>* \<Psi>"
  and     "A\<^sub>G \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>F \<sharp>* A\<^sub>G"
  and     "A\<^sub>F \<sharp>* P"
  and     "A\<^sub>G \<sharp>* P"
  and     "A\<^sub>P \<sharp>* A\<^sub>F"
  and     "A\<^sub>P \<sharp>* A\<^sub>G"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>F"
  and     "A\<^sub>P \<sharp>* \<Psi>\<^sub>G"
  and     "A\<^sub>P \<sharp>* P"

  shows "\<Psi>\<^sub>G \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
using PChain FrP \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> 
proof(induct rule: tauChainInduct2)
  case TauBase
  thus ?case by simp
next
  case(TauStep P P' P'')
  have FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" by fact
  then have PChain: "\<Psi>\<^sub>G \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'" using \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* P\<close> by(rule TauStep)
  then obtain A\<^sub>P' \<Psi>\<^sub>P' \<Psi>' where FrP': "extractFrame P' = \<langle>A\<^sub>P', \<Psi>\<^sub>P'\<rangle>" and "\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'"
                            and "A\<^sub>P' \<sharp>* A\<^sub>F" and "A\<^sub>P' \<sharp>* A\<^sub>G" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>F" and "A\<^sub>P' \<sharp>* \<Psi>\<^sub>G"
                            and "distinct A\<^sub>P'"
                
    using FrP \<open>distinct A\<^sub>P\<close> \<open>A\<^sub>P \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* \<Psi>\<^sub>G\<close>
    by(rule_tac C="(A\<^sub>F, A\<^sub>G, \<Psi>\<^sub>F, \<Psi>\<^sub>G)" in expandTauChainFrame) auto

  from PChain \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> have "A\<^sub>F \<sharp>* P'" and "A\<^sub>G \<sharp>* P'" by(blast dest: tauChainFreshChain)+

  with \<open>A\<^sub>F \<sharp>* P\<close> \<open>A\<^sub>G \<sharp>* P\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P \<sharp>* A\<^sub>G\<close>\<open>A\<^sub>P' \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>G\<close> FrP FrP'
  have "A\<^sub>F \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>P" and "A\<^sub>F \<sharp>* \<Psi>\<^sub>P'" and "A\<^sub>G \<sharp>* \<Psi>\<^sub>P'"
    by(auto dest: extractFrameFreshChain)

  from FeqG have FeqG: "insertAssertion (\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>' \<hookrightarrow>\<^sub>F insertAssertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>'"
    by blast
  obtain p::"name prm" where "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F" and  "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P'" and "(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'"
                         and Sp: "(set p) \<subseteq> set A\<^sub>F \<times> set(p \<bullet> A\<^sub>F)" and "distinctPerm p"
      by(rule_tac xvec=A\<^sub>F and c="(\<Psi>\<^sub>F, \<Psi>\<^sub>P, \<Psi>', \<Psi>\<^sub>P')" in name_list_avoiding) auto
  obtain q::"name prm" where "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G" and  "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P" and "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P'" and "(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>'"
                         and Sq: "(set q) \<subseteq> set A\<^sub>G \<times> set(q \<bullet> A\<^sub>G)" and "distinctPerm q"
    by(rule_tac xvec=A\<^sub>G and c="(\<Psi>\<^sub>G, \<Psi>\<^sub>P, \<Psi>', \<Psi>\<^sub>P')" in name_list_avoiding) auto
  from \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close> have "\<langle>(p \<bullet> A\<^sub>F), ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P')\<rangle> \<simeq>\<^sub>F \<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>')\<rangle>"
    by(rule frameIntCompositionSym[OF AssertionStatEqSym])
  hence "\<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P'\<rangle> \<simeq>\<^sub>F \<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle>"
    by(metis frameIntAssociativity FrameStatEqTrans frameIntCommutativity FrameStatEqSym)
  moreover from FeqG \<open>A\<^sub>F \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>'\<close> Sp
  have "\<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F insertAssertion (\<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P\<rangle>) \<Psi>'"
    apply(erule_tac rev_mp) by(subst frameChainAlpha) (auto simp add: eqvts)
  hence "\<langle>(p \<bullet> A\<^sub>F), \<Psi>' \<otimes> ((p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P)\<rangle> \<hookrightarrow>\<^sub>F  (\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P\<rangle>)"
    using \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P\<close> \<open>(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G\<close> \<open>(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>'\<close> Sq
    apply(erule_tac rev_mp) by(subst frameChainAlpha) (auto simp add: eqvts)
  moreover have "\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> ((q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P)\<rangle> \<simeq>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> (\<Psi>\<^sub>P \<otimes> \<Psi>')\<rangle>"
    by(metis frameIntAssociativity FrameStatEqTrans frameIntCommutativity FrameStatEqSym)
  hence "\<langle>(q \<bullet> A\<^sub>G), \<Psi>' \<otimes> ((q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P)\<rangle> \<simeq>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>" using \<open>\<Psi>\<^sub>P \<otimes> \<Psi>' \<simeq> \<Psi>\<^sub>P'\<close>
    by(blast intro: FrameStatEqTrans frameIntCompositionSym)
  ultimately have "\<langle>(p \<bullet> A\<^sub>F), (p \<bullet> \<Psi>\<^sub>F) \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(rule FrameStatEqImpCompose)
  with \<open>A\<^sub>F \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(p \<bullet> A\<^sub>F) \<sharp>* \<Psi>\<^sub>F\<close> Sp have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>(q \<bullet> A\<^sub>G), (q \<bullet> \<Psi>\<^sub>G) \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(subst frameChainAlpha) (auto simp add: eqvts)
  with \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>P'\<close> \<open>(q \<bullet> A\<^sub>G) \<sharp>* \<Psi>\<^sub>G\<close> Sq have "\<langle>A\<^sub>F, \<Psi>\<^sub>F \<otimes> \<Psi>\<^sub>P'\<rangle> \<hookrightarrow>\<^sub>F \<langle>A\<^sub>G, \<Psi>\<^sub>G \<otimes> \<Psi>\<^sub>P'\<rangle>"
    by(subst frameChainAlpha) (auto simp add: eqvts)
  
  with \<open>\<Psi>\<^sub>F \<rhd> P' \<longmapsto>\<tau> \<prec> P''\<close> FrP' \<open>distinct A\<^sub>P'\<close>
       \<open>A\<^sub>F \<sharp>* P'\<close> \<open>A\<^sub>G \<sharp>* P'\<close> \<open>A\<^sub>F \<sharp>* \<Psi>\<^sub>G\<close> \<open>A\<^sub>G \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>F\<close> \<open>A\<^sub>P' \<sharp>* A\<^sub>G\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>F\<close> \<open>A\<^sub>P' \<sharp>* \<Psi>\<^sub>G\<close>
  have "\<Psi>\<^sub>G \<rhd> P' \<longmapsto>\<tau> \<prec> P''" by(rule_tac transferTauFrame)
  with PChain show ?case by(simp add: r_into_rtrancl rtrancl_into_rtrancl)
qed

coinductive quiet :: "('a, 'b, 'c) psi \<Rightarrow> bool"
  where "\<lbrakk>\<forall>\<Psi>. (insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle> \<and> 
              (\<forall>Rs. \<Psi> \<rhd> P \<longmapsto> Rs \<longrightarrow> (\<exists>P'. Rs = \<tau> \<prec> P' \<and> quiet P')))\<rbrakk> \<Longrightarrow> quiet P"

lemma quietFrame:
  fixes \<Psi> :: 'b
  and   P    :: "('a, 'b, 'c) psi"

  assumes "quiet P"

  shows "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
using assms
by(erule_tac quiet.cases) force
  
lemma quietTransition:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Rs :: "('a, 'b, 'c) residual"

  assumes "quiet P"
  and     "\<Psi> \<rhd> P \<longmapsto> Rs"

  obtains P' where "Rs = \<tau> \<prec> P'" and "quiet P'"
using assms
by(erule_tac quiet.cases) force
  
lemma quietEqvt:
  fixes P :: "('a, 'b, 'c) psi"
  and   p :: "name prm"

  assumes "quiet P"

  shows "quiet(p \<bullet> P)"
proof -
  let ?X = "\<lambda>P. \<exists>p::name prm. quiet(p \<bullet> P)"
  from assms have "?X (p \<bullet> P)" by(rule_tac x="rev p" in exI) auto
  thus ?thesis
    apply coinduct
    apply(clarify)
    apply(rule_tac x=x in exI)
    apply auto
    apply(drule_tac \<Psi>="p \<bullet> \<Psi>" in quietFrame)
    apply(drule_tac p="rev p" in FrameStatEqClosed)
    apply(simp add: eqvts)
    apply(drule_tac pi=p in semantics.eqvt)
    apply(erule_tac quietTransition)
    apply assumption
    apply(rule_tac x="rev p \<bullet> P'" in exI)
    apply auto
    apply(drule_tac pi="rev p" in pt_bij3)
    apply(simp add: eqvts)
    apply(rule_tac x=p in exI)
    by simp
qed
  

lemma quietOutput:
  fixes \<Psi>   :: 'b
  and   P    :: "('a, 'b, 'c) psi"
  and   M    :: 'a
  and   xvec :: "name list"
  and   N    :: 'a
  and   P'   :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>\<nu>*xvec\<rparr>\<langle>N\<rangle> \<prec> P'"
  and     "quiet P"

  shows False
using assms
apply(erule_tac quiet.cases)
by(force simp add: residualInject)

lemma quietInput:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   M  :: 'a
  and   N  :: 'a
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>M\<lparr>N\<rparr> \<prec> P'"
  and     "quiet P"

  shows False
using assms
by(erule_tac quiet.cases) (force simp add: residualInject)

lemma quietTau:
  fixes \<Psi> :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"
  
  assumes "\<Psi> \<rhd> P \<longmapsto>\<tau> \<prec> P'"
  and     "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F \<langle>\<epsilon>, \<Psi>\<rangle>"
  and     "quiet P"

  shows "quiet P'"
using assms
by(erule_tac quiet.cases) (force simp add: residualInject)

lemma tauChainCases[consumes 1, case_names TauBase TauStep]:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   P' :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<Longrightarrow>\<^sup>^\<^sub>\<tau> P'"
  and     "P = P' \<Longrightarrow> Prop"
  and     "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> Prop"

  shows Prop
using assms
by(blast elim: rtranclE dest: rtrancl_into_trancl1)

end

end
