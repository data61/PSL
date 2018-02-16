(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Pres
  imports Weak_Cong Weak_Bisim_Pres Weak_Cong_Sim_Pres
begin

lemma actPres:
  fixes P :: ccs
  and   Q :: ccs
  and   \<alpha> :: act

  assumes "P \<cong> Q"

  shows "\<alpha>.(P) \<cong> \<alpha>.(Q)"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  from `P \<cong> Q` have "P \<approx> Q" by(rule weakCongruenceWeakBisimulation)
  thus ?case by(rule actPres)
qed

lemma sumPres:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<cong> Q"

  shows "P \<oplus> R \<cong> Q \<oplus> R"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  from `P \<cong> Q` have "P \<leadsto><weakBisimulation> Q" by(rule weakCongruenceE)
  thus ?case using Weak_Bisim.reflexive
    by(rule_tac sumPres) auto
qed

lemma parPres:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<cong> Q"

  shows "P \<parallel> R \<cong> Q \<parallel> R"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  from `P \<cong> Q` have "P \<leadsto><weakBisimulation> Q" by(rule weakCongruenceE)
  moreover from `P \<cong> Q` have "P \<approx> Q" by(rule weakCongruenceWeakBisimulation)
  ultimately show ?case using Weak_Bisim_Pres.parPres
    by(rule parPres)
qed

lemma resPres: 
  fixes P :: ccs
  and   Q :: ccs
  and   x :: name

  assumes "P \<cong> Q"

  shows "\<lparr>\<nu>x\<rparr>P \<cong> \<lparr>\<nu>x\<rparr>Q"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  from `P \<cong> Q` have "P \<leadsto><weakBisimulation> Q" by(rule weakCongruenceE)
  thus ?case using Weak_Bisim_Pres.resPres
    by(rule resPres)
qed

lemma weakBisimBangRel: "bangRel weakBisimulation \<subseteq> weakBisimulation"
proof auto
  fix P Q
  assume "(P, Q) \<in> bangRel weakBisimulation"
  thus "P \<approx> Q"
  proof(induct rule: bangRel.induct)
    case(BRBang P Q)
    from `P \<approx> Q` show "!P \<approx> !Q" by(rule Weak_Bisim_Pres.bangPres)
  next
    case(BRPar R T P Q)
    from `R \<approx> T` have "R \<parallel> P \<approx> T \<parallel> P" by(rule Weak_Bisim_Pres.parPres)
    moreover from `P \<approx> Q` have "P \<parallel> T \<approx> Q \<parallel> T" by(rule Weak_Bisim_Pres.parPres)
    hence "T \<parallel> P \<approx> T \<parallel> Q" by(metis bisimWeakBisimulation Weak_Bisim.transitive parComm)
    ultimately show "R \<parallel> P \<approx> T \<parallel> Q" by(rule Weak_Bisim.transitive)
  qed
qed

lemma bangPres:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<cong> Q"

  shows "!P \<cong> !Q"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  let ?X = "{(P, Q) | P Q. P \<cong> Q}"
  from `P \<cong> Q` have "(P, Q) \<in> ?X" by auto
  moreover have "\<And>P Q. (P, Q) \<in> ?X \<Longrightarrow> P \<leadsto><weakBisimulation> Q" by(auto dest: weakCongruenceE)
  moreover have "?X \<subseteq> weakBisimulation" by(auto intro: weakCongruenceWeakBisimulation)
  ultimately have "!P \<leadsto><bangRel weakBisimulation> !Q" by(rule bangPres)
  thus ?case using weakBisimBangRel by(rule Weak_Cong_Sim.weakMonotonic)
qed

end
