(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Cong
  imports Weak_Early_Bisim Weak_Early_Step_Sim Strong_Early_Bisim
begin

definition weakCongruence :: "pi \<Rightarrow> pi \<Rightarrow> bool" (infixr "\<simeq>" 65)
where "P \<simeq> Q \<equiv> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q \<and> Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"

lemma weakCongISym[consumes 1, case_names cSym cSim]:
  fixes P :: pi
  and   Q :: pi

  assumes "Prop P Q"
  and     "\<And>R S. Prop R S \<Longrightarrow> Prop S R"
  and     "\<And>R S. Prop R S \<Longrightarrow> (F R) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (F S)"

  shows "F P \<simeq> F Q"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongISym2[consumes 1, case_names cSim]:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq> Q"
  and     "\<And>R S. R \<simeq> S \<Longrightarrow> (F R) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (F S)"

  shows "F P \<simeq> F Q"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongEE:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq> Q"

  shows "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
  and   "Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"
using assms
by(auto simp add: weakCongruence_def)

lemma weakCongI:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
  and     "Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"

  shows "P \<simeq> Q"
using assms
by(auto simp add: weakCongruence_def)

lemma eqvtI[eqvt]:
  fixes P :: pi
  and   Q :: pi
  and   p :: "name prm"

  assumes "P \<simeq> Q"

  shows "(p \<bullet> P) \<simeq> (p \<bullet> Q)"
using assms
by(auto simp add: weakCongruence_def intro: eqvtI)

lemma strongBisimWeakCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"

  shows "P \<simeq> Q"
proof -
  have "\<And>P Q. P \<leadsto>[bisim] Q \<Longrightarrow> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
  proof -
    fix P Q
    assume "P \<leadsto>[bisim] Q"
    hence "P \<leadsto>\<guillemotleft>bisim\<guillemotright> Q" by(rule Weak_Early_Step_Sim.strongSimWeakSim)
    moreover have "bisim \<subseteq> weakBisim"
      by(auto intro: strongBisimWeakBisim)
    ultimately show "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(rule Weak_Early_Step_Sim.monotonic)
  qed
  with assms show ?thesis
    by(blast intro: weakCongI dest: Strong_Early_Bisim.bisimE)
qed

lemma congruenceWeakBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq> Q"

  shows "P \<approx> Q"
using assms
proof -
  let ?X = "{(P, Q) | P Q. P \<simeq> Q}"
  from assms have "(P, Q) \<in> ?X" by simp
  thus ?thesis 
  proof(induct rule: weakBisimCoinduct)
    case(cSim P Q) 
    {
      fix P Q
      assume "P \<simeq> Q"
      hence "P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(simp add: weakCongruence_def)
      hence "P \<leadsto>\<guillemotleft>(?X \<union> weakBisim)\<guillemotright> Q" by(rule_tac Weak_Early_Step_Sim.monotonic) auto
      hence "P \<leadsto><(?X \<union> weakBisim)> Q" by(rule weakSimWeakEqSim)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto simp add: weakCongruence_def)
  qed
qed

lemma reflexive:
  fixes P :: pi
  
  shows "P \<simeq> P"
proof -
  from Weak_Early_Bisim.reflexive have "\<And>P. P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"
    by(blast intro: Weak_Early_Step_Sim.reflexive)
  thus ?thesis
    by(force simp add: substClosed_def weakCongruence_def)
qed

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"
  
  shows "Q \<simeq> P"
using assms
by(force simp add: substClosed_def weakCongruence_def)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<simeq> Q"
  and     "Q \<simeq> R"
  
  shows "P \<simeq> R"
proof -
  have Goal: "\<And>P Q R. \<lbrakk>P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q; Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> R; P \<approx> Q\<rbrakk> \<Longrightarrow> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> R"
    using Weak_Early_Bisim.eqvt Weak_Early_Bisim.weakBisimE Weak_Early_Bisim.transitive
    by(blast intro: Weak_Early_Step_Sim.transitive)
  from assms show ?thesis
    apply(simp add: weakCongruence_def) using assms
    by(blast intro: Goal dest: congruenceWeakBisim symetric)
qed

end
