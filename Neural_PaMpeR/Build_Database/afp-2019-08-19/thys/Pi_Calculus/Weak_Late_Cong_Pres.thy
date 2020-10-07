(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong_Pres
  imports Weak_Late_Cong Weak_Late_Step_Sim_Pres Weak_Late_Bisim_Pres
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "\<tau>.(P) \<simeq> \<tau>.(Q)"
using assms
by(blast intro: unfoldI Weak_Late_Step_Sim_Pres.tauPres dest: congruenceWeakBisim symetric)

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "a{b}.P \<simeq> a{b}.Q"
using assms
by(blast intro: unfoldI Weak_Late_Step_Sim_Pres.outputPres dest: congruenceWeakBisim symetric)

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PSimQ: "\<forall>y. P[x::=y] \<simeq> Q[x::=y]"
  
  shows "a<x>.P \<simeq> a<x>.Q"
using assms
apply(rule_tac unfoldI)
apply(rule_tac Weak_Late_Step_Sim_Pres.inputPres, auto intro: congruenceWeakBisim)
by(rule_tac Weak_Late_Step_Sim_Pres.inputPres, auto intro: congruenceWeakBisim Weak_Late_Bisim.symmetric)

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq> Q"

  shows "[a\<frown>b]P \<simeq> [a\<frown>b]Q"
using assms
by(blast intro: unfoldI Weak_Late_Step_Sim_Pres.matchPres dest: unfoldE symetric)

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq> Q"

  shows "[a\<noteq>b]P \<simeq> [a\<noteq>b]Q"
using assms
by(blast intro: unfoldI Weak_Late_Step_Sim_Pres.mismatchPres dest: unfoldE symetric)

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq> Q"

  shows "P \<oplus> R \<simeq> Q \<oplus> R"
using assms
by(blast intro: Weak_Late_Bisim.reflexive unfoldI Weak_Late_Step_Sim_Pres.sumPres dest: unfoldE symetric)

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq> Q"

  shows "P \<parallel> R \<simeq> Q \<parallel> R"
proof -
  have "\<And>P Q R. \<lbrakk>P \<leadsto><weakBisim> Q; P \<approx> Q\<rbrakk> \<Longrightarrow> P \<parallel> R \<leadsto><weakBisim> Q \<parallel> R"
  proof -
    fix P Q R
    assume "P \<leadsto><weakBisim> Q" and "P \<approx> Q"
    thus "P \<parallel> R \<leadsto><weakBisim> Q \<parallel> R"
      using Weak_Late_Bisim_Pres.parPres Weak_Late_Bisim_Pres.resPres Weak_Late_Bisim.reflexive Weak_Late_Bisim.eqvt
      by(blast intro: Weak_Late_Step_Sim_Pres.parPres)
  qed
  with assms show ?thesis
    by(blast intro: unfoldI dest: congruenceWeakBisim unfoldE symetric)
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PeqQ: "P \<simeq> Q"
  
  shows "<\<nu>x>P \<simeq> <\<nu>x>Q"
proof -
  have "\<And>P Q x. P \<leadsto><weakBisim> Q \<Longrightarrow> <\<nu>x>P \<leadsto><weakBisim> <\<nu>x>Q"
  proof -
    fix P Q x
    assume "P \<leadsto><weakBisim> Q"
    with Weak_Late_Bisim.eqvt Weak_Late_Bisim_Pres.resPres show "<\<nu>x>P \<leadsto><weakBisim> <\<nu>x>Q"
      by(blast intro: Weak_Late_Step_Sim_Pres.resPres)
  qed
  with assms show ?thesis
    by(blast intro: unfoldI dest: congruenceWeakBisim unfoldE symetric)
qed

lemma congruenceBang:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq> Q"

  shows "!P \<simeq> !Q"
proof -
  have "\<And>P Q. \<lbrakk>P \<leadsto><weakBisim> Q; P \<simeq> Q\<rbrakk> \<Longrightarrow> !P \<leadsto><weakBisim> !Q"
  proof -
    fix P Q
    assume "P \<leadsto><weakBisim> Q" and "P \<simeq> Q"
    hence "!P \<leadsto><bangRel weakBisim> !Q" using unfoldE(1) congruenceWeakBisim Weak_Late_Bisim.eqvt 
      by(rule Weak_Late_Step_Sim_Pres.bangPres)
    moreover have "bangRel weakBisim \<subseteq> weakBisim"
      proof auto
        fix a b
        assume "(a, b) \<in> bangRel weakBisim"
        thus   "a \<approx> b"
          apply(induct rule: bangRel.induct)
          apply (metis Weak_Late_Bisim_Pres.bangPres)
          apply (metis Weak_Late_Bisim.reflexive Weak_Late_Bisim.symmetric Weak_Late_Bisim.transitive Weak_Late_Bisim_Pres.parPres Weak_Late_Bisim_SC.parSym)
          by (metis Weak_Late_Bisim_Pres.resPres)
      qed
    ultimately show"!P \<leadsto><weakBisim> !Q" 
      by(rule Weak_Late_Step_Sim.monotonic)
  qed

  with assms show ?thesis
    by(blast intro: unfoldI dest: unfoldE symetric congruenceWeakBisim)
qed

end
