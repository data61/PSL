(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong
  imports Weak_Late_Bisim Weak_Late_Step_Sim Strong_Late_Bisim
begin

definition congruence :: "(pi \<times> pi) set" where 
  "congruence \<equiv> {(P, Q) |P Q. P \<leadsto><weakBisim> Q \<and> Q \<leadsto><weakBisim> P}"
abbreviation congruenceJudge (infixr "\<simeq>" 65) where "P \<simeq> Q \<equiv> (P, Q) \<in> congruence"

lemma unfoldE:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq> Q"

  shows "P \<leadsto><weakBisim> Q"
  and   "Q \<leadsto><weakBisim> P"
proof -
  from assms show "P \<leadsto><weakBisim> Q" by(force simp add: congruence_def)
next
  from assms show "Q \<leadsto><weakBisim> P" by(force simp add: congruence_def)
qed

lemma unfoldI:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<leadsto><weakBisim> Q"
  and     "Q \<leadsto><weakBisim> P"

  shows "P \<simeq> Q"
using assms by(force simp add: congruence_def)


lemma eqvt:
  shows "eqvt congruence"
proof -
  have "\<And>P Q (perm::name prm). P \<leadsto><weakBisim> Q \<Longrightarrow> (perm \<bullet> P) \<leadsto><weakBisim> (perm \<bullet> Q)"
  proof -
    fix P Q perm
    assume "P \<leadsto><weakBisim> Q"
    thus "((perm::name prm) \<bullet> P) \<leadsto><weakBisim> (perm \<bullet> Q)"
      apply -
      by(blast intro: Weak_Late_Step_Sim.eqvtI Weak_Late_Bisim.eqvt)
  qed
  thus ?thesis
    by(simp add: congruence_def eqvt_def)
qed

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<simeq> Q"

  shows "(perm \<bullet> P) \<simeq> (perm \<bullet> Q)"
using assms
by(rule eqvtRelI[OF eqvt])

lemma strongBisimWeakEq:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"

  shows "P \<simeq> Q"
proof -
  have "\<And>P Q. P \<leadsto>[bisim] Q \<Longrightarrow> P \<leadsto><weakBisim> Q"
  proof -
    fix P Q
    assume "P \<leadsto>[bisim] Q"
    hence "P \<leadsto><bisim> Q" by(rule strongSimWeakEqSim)
    moreover have "bisim \<subseteq> weakBisim"
      by(auto intro: strongBisimWeakBisim)
    ultimately show "P \<leadsto><weakBisim> Q" by(rule Weak_Late_Step_Sim.monotonic)
  qed
  with assms show ?thesis
    by(blast intro: unfoldI dest: Strong_Late_Bisim.bisimE Strong_Late_Bisim.symmetric)
qed

lemma congruenceWeakBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq> Q"

  shows "P \<approx> Q"
proof -
  let ?X = "{(P, Q) | P Q. P \<simeq> Q}"
  from assms have "(P, Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P Q)
    {
      fix P Q
      assume "P \<simeq> Q"
      hence "P \<leadsto><weakBisim> Q" by(simp add: congruence_def)
      hence "P \<leadsto><(?X \<union> weakBisim)> Q" by(rule_tac Weak_Late_Step_Sim.monotonic) auto
      hence "P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> Q" by(rule Weak_Late_Step_Sim.weakSimWeakEqSim)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto simp add: congruence_def)
  qed 
qed

lemma congruenceSubsetWeakBisim:
  shows "congruence \<subseteq> weakBisim"
by(auto intro: congruenceWeakBisim)

lemma reflexive:
  fixes P :: pi
  
  shows "P \<simeq> P"
proof -
  from Weak_Late_Bisim.reflexive have "\<And>P. P \<leadsto><weakBisim> P"
    by(blast intro: Weak_Late_Step_Sim.reflexive)
  thus ?thesis
    by(force simp add: substClosed_def congruence_def)
qed

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"
  
  shows "Q \<simeq> P"
using assms
by(force simp add: substClosed_def congruence_def)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<simeq> Q"
  and     "Q \<simeq> R"
  
  shows "P \<simeq> R"
proof -
  have Goal: "\<And>P Q R. \<lbrakk>P \<leadsto><weakBisim> Q; Q \<leadsto><weakBisim> R; P \<approx> Q\<rbrakk> \<Longrightarrow> P \<leadsto><weakBisim> R"
    using Weak_Late_Bisim.eqvt Weak_Late_Bisim.unfoldE Weak_Late_Bisim.transitive
    by(blast intro: Weak_Late_Step_Sim.transitive)
  from assms show ?thesis
    apply(simp add: congruence_def) using assms
    by(blast intro: Goal dest: congruenceWeakBisim symetric)
qed

end
