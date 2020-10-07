(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Cong_Subst_Pres
  imports Weak_Early_Cong_Subst Weak_Early_Cong_Pres
begin

lemma weakCongStructCong:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<simeq>\<^sup>s Q"
using assms
by(metis earlyCongStructCong strongEqWeakCong)


lemma tauPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "\<tau>.(P) \<simeq>\<^sup>s \<tau>.(Q)"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.tauPres)

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PeqQ: "P \<simeq>\<^sup>s Q"

  shows "a<x>.P \<simeq>\<^sup>s a<x>.Q"
proof(auto simp add: weakCongruenceSubst_def)
  fix s::"(name \<times> name) list"

  from congruenceWeakBisim have Input: "\<And>P Q a x s. \<lbrakk>P[<s>] \<simeq>\<^sup>s Q[<s>]; x \<sharp> s\<rbrakk> \<Longrightarrow> (a<x>.P)[<s>] \<simeq> (a<x>.Q)[<s>]"
    apply(auto simp add: weakCongruenceSubst_def weakCongruence_def)
    apply(rule Weak_Early_Step_Sim_Pres.inputPres, auto)
    apply(erule_tac x="[(x, y)]" in allE, auto)
    apply(rule Weak_Early_Step_Sim_Pres.inputPres, auto)
    by(erule_tac x="[(x, y)]" in allE, auto)

  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force intro: name_exists_fresh[of "(P, Q, s)"])

  from PeqQ have "P[<([(x, c)] \<bullet> s)>] \<simeq>\<^sup>s Q[<([(x, c)] \<bullet> s)>]" by(rule partUnfold)
  hence "([(x, c)] \<bullet> P[<([(x, c)] \<bullet> s)>]) \<simeq>\<^sup>s  ([(x, c)] \<bullet> Q[<([(x, c)] \<bullet> s)>])" by(rule Weak_Early_Cong_Subst.eqvtI)
  hence "([(x, c)] \<bullet> P)[<s>] \<simeq>\<^sup>s ([(x, c)] \<bullet> Q)[<s>]" by simp
  hence "(a<c>.([(x, c)] \<bullet> P))[<s>] \<simeq> (a<c>.([(x, c)] \<bullet> Q))[<s>]" using cFreshs by(rule Input)

  moreover from cFreshP cFreshQ have "a<x>.P = a<c>.([(x, c)] \<bullet> P)" and "a<x>.Q = a<c>.([(x, c)] \<bullet> Q)"
    by(simp add: Agent.alphaInput)+

  ultimately show "(a<x>.P)[<s>] \<simeq> (a<x>.Q)[<s>]" by simp
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "a{b}.P \<simeq>\<^sup>s a{b}.Q"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.outputPres)

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq>\<^sup>s Q"

  shows "[a\<frown>b]P \<simeq>\<^sup>s [a\<frown>b]Q"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.matchPres)

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq>\<^sup>s Q"

  shows "[a\<noteq>b]P \<simeq>\<^sup>s [a\<noteq>b]Q"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.mismatchPres)

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<oplus> R \<simeq>\<^sup>s Q \<oplus> R"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.sumPres)

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<parallel> R \<simeq>\<^sup>s Q \<parallel> R"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.parPres)

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PeqQ: "P \<simeq>\<^sup>s Q"
  
  shows "<\<nu>x>P \<simeq>\<^sup>s <\<nu>x>Q"
proof(auto simp add: weakCongruenceSubst_def)
  fix s::"(name \<times> name) list"

  have Goal: "\<And>P Q x s. \<lbrakk>P[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q[<s>]; x \<sharp> s\<rbrakk> \<Longrightarrow> (<\<nu>x>P)[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (<\<nu>x>Q)[<s>]"
    by(force intro: Weak_Early_Step_Sim_Pres.resPres Weak_Early_Bisim_Pres.resPres Weak_Early_Bisim.eqvt)
  
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force intro: name_exists_fresh[of "(P, Q, s)"])

  from PeqQ have "P[<([(x, c)] \<bullet> s)>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q[<([(x, c)] \<bullet> s)>]" and 
                 "Q[<([(x, c)] \<bullet> s)>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P[<([(x, c)] \<bullet> s)>]"
    by(force simp add: weakCongruenceSubst_def weakCongruence_def)+

  hence "([(x, c)] \<bullet> (P[<([(x, c)] \<bullet> s)>])) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, c)] \<bullet> (Q[<([(x, c)] \<bullet> s)>]))" and 
        "([(x, c)] \<bullet> (Q[<([(x, c)] \<bullet> s)>])) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, c)] \<bullet> (P[<([(x, c)] \<bullet> s)>]))"
    by(blast intro: Weak_Early_Step_Sim.eqvtI Weak_Early_Bisim.eqvt)+

  hence "([(x, c)] \<bullet> P)[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, c)] \<bullet> Q)[<s>]" and
        "([(x, c)] \<bullet> Q)[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> ([(x, c)] \<bullet> P)[<s>]" by simp+

  with cFreshs have "(<\<nu>c>([(x, c)] \<bullet> P))[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (<\<nu>c>([(x, c)] \<bullet> Q))[<s>]" and
                    "(<\<nu>c>([(x, c)] \<bullet> Q))[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (<\<nu>c>([(x, c)] \<bullet> P))[<s>]"
    by(blast intro: Goal)+

  moreover from cFreshP cFreshQ have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" and "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)"
    by(simp add: alphaRes)+

  ultimately show "(<\<nu>x>P)[<s>] \<simeq> (<\<nu>x>Q)[<s>]"
    by(simp add: weakCongruence_def)
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "!P \<simeq>\<^sup>s !Q"
using assms
by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong_Pres.bangPres)

end
