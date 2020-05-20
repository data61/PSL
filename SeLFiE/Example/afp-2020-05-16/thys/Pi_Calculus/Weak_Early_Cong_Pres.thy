(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Cong_Pres
  imports Weak_Early_Cong Weak_Early_Step_Sim_Pres Weak_Early_Bisim_Pres
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "\<tau>.(P) \<simeq> \<tau>.(Q)"
proof -
  from assms have "P \<approx> Q" by(rule congruenceWeakBisim)
  thus ?thesis by(force intro: Weak_Early_Step_Sim_Pres.tauPres simp add: weakCongruence_def dest: weakBisimE(2))
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "a{b}.P \<simeq> a{b}.Q"
proof -
  from assms have "P \<approx> Q" by(rule congruenceWeakBisim)
  thus ?thesis by(force intro: Weak_Early_Step_Sim_Pres.outputPres simp add: weakCongruence_def dest: weakBisimE(2))
qed

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq> Q"

  shows "[a\<frown>b]P \<simeq> [a\<frown>b]Q"
using assms
by(auto simp add: weakCongruence_def intro: Weak_Early_Step_Sim_Pres.matchPres)

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq> Q"

  shows "[a\<noteq>b]P \<simeq> [a\<noteq>b]Q"
using assms
by(auto simp add: weakCongruence_def intro: Weak_Early_Step_Sim_Pres.mismatchPres)

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq> Q"

  shows "P \<oplus> R \<simeq> Q \<oplus> R"
using assms
by(auto simp add: weakCongruence_def intro: Weak_Early_Step_Sim_Pres.sumPres Weak_Early_Bisim.reflexive)

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq> Q"

  shows "P \<parallel> R \<simeq> Q \<parallel> R"
proof -
  have "\<And>P Q R. \<lbrakk>P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q; P \<approx> Q\<rbrakk> \<Longrightarrow> P \<parallel> R \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q \<parallel> R"
  proof -
    fix P Q R
    assume "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" and "P \<approx> Q"
    thus "P \<parallel> R \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q \<parallel> R"
      using Weak_Early_Bisim_Pres.parPres Weak_Early_Bisim_Pres.resPres Weak_Early_Bisim.reflexive Weak_Early_Bisim.eqvt
      by(blast intro: Weak_Early_Step_Sim_Pres.parPres)
  qed
  moreover from assms have "P \<approx> Q" by(rule congruenceWeakBisim)
  ultimately show ?thesis using assms
    by(auto simp add: weakCongruence_def dest: weakBisimE)
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PeqQ: "P \<simeq> Q"
  
  shows "<\<nu>x>P \<simeq> <\<nu>x>Q"
proof -
  have "\<And>P Q x. P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q \<Longrightarrow> <\<nu>x>P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> <\<nu>x>Q"
  proof -
    fix P Q x
    assume "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
    with Weak_Early_Bisim.eqvt Weak_Early_Bisim_Pres.resPres show "<\<nu>x>P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> <\<nu>x>Q"
      by(blast intro: Weak_Early_Step_Sim_Pres.resPres)
  qed
  with assms show ?thesis by(simp add: weakCongruence_def)
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "!P \<simeq> !Q"
using assms
proof(induct rule: weakCongISym2)
  case(cSim P Q)
  let ?X = "{(P, Q) | P Q. P \<simeq> Q}"
  from \<open>P \<simeq> Q\<close>  have "(P, Q) \<in> ?X"  by auto
  moreover have "\<And>P Q. (P, Q) \<in> ?X \<Longrightarrow> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(auto simp add: weakCongruence_def)
  moreover from congruenceWeakBisim have "?X \<subseteq> weakBisim" by auto
  ultimately have "!P \<leadsto>\<guillemotleft>bangRel weakBisim\<guillemotright> !Q" using Weak_Early_Bisim.eqvt 
    by(rule Weak_Early_Step_Sim_Pres.bangPres)
  moreover have "bangRel weakBisim \<subseteq> weakBisim" by(rule bangRelSubWeakBisim)
  ultimately show "!P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> !Q"
    by(rule Weak_Early_Step_Sim.monotonic)
qed
  
end
