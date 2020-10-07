(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Simulation
  imports Weak_Simulation Tau_Chain
begin

context env begin

definition
  "weakCongSimulation" :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow>
                       ('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set \<Rightarrow> 
                       ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<leadsto>\<guillemotleft>_\<guillemotright> _" [80, 80, 80, 80] 80)
where
  "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q \<equiv> \<forall>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<longrightarrow> (\<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel)"

abbreviation
  weakCongSimulationNilJudge ("_ \<leadsto>\<guillemotleft>_\<guillemotright> _" [80, 80, 80] 80) where "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q \<equiv> SBottom' \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

lemma weakCongSimI[case_names cTau]:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   C   :: "'d::fs_name"

  assumes rTau:  "\<And>Q'. \<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<exists>P'. \<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P' \<and> (\<Psi>, P', Q') \<in> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
using assms
by(auto simp add: weakCongSimulation_def)


lemma weakCongSimE:
  fixes F   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'"

  obtains P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
using assms
by(auto simp add: weakCongSimulation_def)

lemma weakCongSimClosedAux:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>\<guillemotleft>Rel\<guillemotright> (p \<bullet> Q)"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>p \<bullet> \<Psi> \<rhd> p \<bullet> Q \<longmapsto>\<tau> \<prec> Q'\<close> 
  have "(rev p \<bullet> p \<bullet> \<Psi>) \<rhd> (rev p \<bullet> p \<bullet> Q) \<longmapsto>(rev p \<bullet> (\<tau> \<prec> Q'))"
    by(blast dest: semantics.eqvt)
  hence "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> (rev p \<bullet> Q')" by(simp add: eqvts)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', rev p \<bullet> Q') \<in> Rel"
    by(blast dest: weakCongSimE)
  from PChain have "(p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')" by(rule tauStepChainEqvt)
  moreover from P'RelQ' EqvtRel have "(p \<bullet> (\<Psi>,  P', rev p \<bullet> Q')) \<in> Rel"
    by(simp only: eqvt_def)
  hence "(p \<bullet> \<Psi>, p \<bullet> P', Q') \<in> Rel" by(simp add: eqvts)
  ultimately show ?case
    by blast
qed

lemma weakCongSimClosed:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   p   :: "name prm"

  assumes EqvtRel: "eqvt Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q \<Longrightarrow> (p \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>\<guillemotleft>Rel\<guillemotright> (p \<bullet> Q)"
  and   "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q \<Longrightarrow> (p \<bullet> P) \<leadsto>\<guillemotleft>Rel\<guillemotright> (p \<bullet> Q)"
using EqvtRel
by(force dest: weakCongSimClosedAux simp add: permBottom)+

lemma weakCongSimReflexive:
  fixes Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"

  assumes "{(\<Psi>, P, P) | \<Psi> P. True} \<subseteq> Rel"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> P"
using assms
by(auto simp add: weakCongSimulation_def dest: rtrancl_into_rtrancl)

lemma weakStepSimTauChain:
  fixes \<Psi>   :: 'b
  and   Q   :: "('a, 'b, 'c) psi"
  and   Q'  :: "('a, 'b, 'c) psi"
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     Sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><Rel> Q"
  
  obtains P' where "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
proof -
  assume A: "\<And>P'. \<lbrakk>\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'; (\<Psi>, P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from \<open>\<Psi> \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'\<close> \<open>\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q\<close> A show ?thesis
  proof(induct arbitrary: P thesis rule: tauStepChainInduct)
    case(TauBase Q Q' P)
    with \<open>\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q\<close> \<open>\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
      by(rule_tac weakCongSimE)
    thus ?case by(rule TauBase)
  next
    case(TauStep Q Q' Q'' P)
    from \<open>\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q\<close> obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and "(\<Psi>, P', Q') \<in> Rel"
      by(rule TauStep)
    from \<open>(\<Psi>, P', Q') \<in> Rel\<close> have "\<Psi> \<rhd> P' \<leadsto><Rel> Q'" by(rule Sim)
    then obtain P'' where P'Chain: "\<Psi> \<rhd> P' \<Longrightarrow>\<^sup>^\<^sub>\<tau> P''" and "(\<Psi>, P'', Q'') \<in> Rel"
      using \<open>\<Psi> \<rhd> Q' \<longmapsto>\<tau> \<prec> Q''\<close> by(blast dest: weakSimE)
    from PChain P'Chain have "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P''" by simp
    thus ?case using \<open>(\<Psi>, P'', Q'') \<in> Rel\<close> by(rule TauStep)
  qed
qed

lemma weakCongSimTransitive:
  fixes \<Psi>     :: 'b
  and   P      :: "('a, 'b, 'c) psi"
  and   Rel    :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q      :: "('a, 'b, 'c) psi"
  and   Rel'   :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   T      :: "('a, 'b, 'c) psi"
  and   Rel''  :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes PRelQ: "(\<Psi>, P, Q) \<in> Rel"
  and     PSimQ: "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     QSimR: "\<Psi> \<rhd> Q \<leadsto>\<guillemotleft>Rel'\<guillemotright> R"
  and     Set: "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. (\<Psi>, P, Q) \<in> Rel \<and> (\<Psi>, Q, R) \<in> Rel'} \<subseteq> Rel''"
  and     Sim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> Rel \<Longrightarrow> \<Psi> \<rhd> P \<leadsto><Rel> Q"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel''\<guillemotright> R"
proof(induct rule: weakCongSimI)
  case(cTau R')
  from QSimR \<open>\<Psi> \<rhd> R \<longmapsto>\<tau> \<prec> R'\<close> obtain Q' where QChain: "\<Psi> \<rhd> Q \<Longrightarrow>\<^sub>\<tau> Q'" and Q'RelR': "(\<Psi>, Q', R') \<in> Rel'" 
    by(blast dest: weakCongSimE)
  from QChain PSimQ Sim obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(rule weakStepSimTauChain)
  moreover from P'RelQ' Q'RelR' Set have "(\<Psi>, P', R') \<in> Rel''" by blast
  ultimately show ?case by blast
qed

lemma weakCongSimStatEq:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b

  assumes PSimQ: "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     "\<Psi> \<simeq> \<Psi>'"
  and     C1: "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>(\<Psi>, P, Q) \<in> Rel; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> Rel'"

  shows "\<Psi>' \<rhd> P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q"
proof(induct rule: weakCongSimI)
  case(cTau Q')
  from \<open>\<Psi>' \<rhd> Q \<longmapsto>\<tau> \<prec> Q'\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
  have "\<Psi> \<rhd> Q \<longmapsto>\<tau> \<prec> Q'" by(metis statEqTransition AssertionStatEqSym)
  with PSimQ obtain P' where PChain: "\<Psi> \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(\<Psi>, P', Q') \<in> Rel"
    by(blast dest: weakCongSimE)
  
  from PChain \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi>' \<rhd> P \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauStepChainStatEq)
  moreover from \<open>(\<Psi>, P', Q') \<in> Rel\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(\<Psi>', P', Q') \<in> Rel'"
    by(rule C1)
  ultimately show ?case by blast
qed

lemma weakCongSimMonotonic: 
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   A :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q :: "('a, 'b, 'c) psi"
  and   B :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>A\<guillemotright> Q"
  and     "A \<subseteq> B"

  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>B\<guillemotright> Q"
using assms
by(simp (no_asm) add: weakCongSimulation_def) (blast dest: weakCongSimE)+

lemma strongSimWeakCongSim:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Rel :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"
  and   Q   :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<leadsto>[Rel] Q"
  and     "Rel \<subseteq> Rel'"
  
  shows "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q"
using assms
apply(auto simp add: simulation_def weakCongSimulation_def)
by(erule_tac x=\<tau> in allE) fastforce

end

end
