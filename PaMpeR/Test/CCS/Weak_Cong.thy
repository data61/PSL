(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong
  imports Weak_Cong_Sim Weak_Bisim Strong_Bisim_SC
begin

definition weakCongruence :: "ccs \<Rightarrow> ccs \<Rightarrow> bool" ("_ \<cong> _" [70, 70] 65)
where
  "P \<cong> Q \<equiv> P \<leadsto><weakBisimulation> Q \<and> Q \<leadsto><weakBisimulation> P"

lemma weakCongruenceE:
  fixes P  :: "ccs"
  and   Q  :: "ccs"

  assumes "P \<cong> Q"

  shows "P \<leadsto><weakBisimulation> Q"
  and   "Q \<leadsto><weakBisimulation> P"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongruenceI:
  fixes P :: "ccs"
  and   Q :: "ccs"

  assumes "P \<leadsto><weakBisimulation> Q"
  and     "Q \<leadsto><weakBisimulation> P"

  shows "P \<cong> Q"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongISym[consumes 1, case_names cSym cSim]:
  fixes P :: ccs
  and   Q :: ccs

  assumes "Prop P Q"
  and     "\<And>P Q. Prop P Q \<Longrightarrow> Prop Q P"
  and     "\<And>P Q. Prop P Q \<Longrightarrow> (F P) \<leadsto><weakBisimulation> (F Q)"

  shows "F P \<cong> F Q"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongISym2[consumes 1, case_names cSim]:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<cong> Q"
  and     "\<And>P Q. P \<cong> Q \<Longrightarrow> (F P) \<leadsto><weakBisimulation> (F Q)"

  shows "F P \<cong> F Q"
using assms
by(auto simp add: weakCongruence_def)

lemma reflexive: 
  fixes P :: ccs

  shows "P \<cong> P"
by(auto intro: weakCongruenceI Weak_Bisim.reflexive Weak_Cong_Sim.reflexive)

lemma symmetric: 
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<cong> Q"

  shows "Q \<cong> P"
using assms  
by(auto simp add: weakCongruence_def)

lemma transitive: 
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<cong> Q"
  and     "Q \<cong> R"

  shows "P \<cong> R"
proof -
  let ?Prop = "\<lambda>P R. \<exists>Q. P \<cong> Q \<and> Q \<cong> R"
  from assms have "?Prop P R" by auto
  thus ?thesis
  proof(induct rule: weakCongISym)
    case(cSym P R)
    thus ?case by(auto dest: symmetric)
  next
    case(cSim P R)
    from `?Prop P R` obtain Q where "P \<cong> Q" and "Q \<cong> R"
      by auto
    from `P \<cong> Q` have "P \<leadsto><weakBisimulation> Q" by(rule weakCongruenceE)
    moreover from `Q \<cong> R` have "Q \<leadsto><weakBisimulation> R" by(rule weakCongruenceE)
    moreover from Weak_Bisim.transitive have "weakBisimulation O weakBisimulation \<subseteq> weakBisimulation"
      by auto
    ultimately show ?case using weakBisimulationE(1)
      by(rule Weak_Cong_Sim.transitive)
  qed
qed

lemma bisimWeakCongruence:
  fixes P :: ccs
  and   Q :: ccs
  
  assumes "P \<sim> Q"

  shows "P \<cong> Q"
using assms
proof(induct rule: weakCongISym)
  case(cSym P Q)
  thus ?case by(rule bisimE)
next
  case(cSim P Q)
  from `P \<sim> Q` have "P \<leadsto>[bisim] Q" by(rule bisimE)
  hence "P \<leadsto>[weakBisimulation] Q" using bisimWeakBisimulation 
    by(rule_tac monotonic) auto
  thus ?case by(rule simWeakSim)
qed

lemma structCongWeakCongruence:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<cong> Q"
using assms
by(auto intro: bisimWeakCongruence bisimStructCong)

lemma weakCongruenceWeakBisimulation:
  fixes P :: ccs
  and   Q :: ccs
  
  assumes "P \<cong> Q"

  shows "P \<approx> Q"
proof -
  let ?X = "{(P, Q) | P Q. P \<cong> Q}"
  from assms have "(P, Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimulationCoinduct)
    case(cSim P Q)
    from `(P, Q) \<in> ?X` have "P \<cong> Q" by auto
    hence "P \<leadsto><weakBisimulation> Q" by(rule Weak_Cong.weakCongruenceE)
    hence "P \<leadsto><(?X \<union> weakBisimulation)> Q" by(force intro: Weak_Cong_Sim.weakMonotonic)
    thus ?case by(rule weakCongSimWeakSim)
  next
    case(cSym P Q)
    from `(P, Q) \<in> ?X` show ?case by(blast dest: symmetric)
  qed
qed


end
