(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong_Subst_Pres
  imports Weak_Late_Cong_Subst Weak_Late_Cong_Pres
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "\<tau>.(P) \<simeq>\<^sup>s \<tau>.(Q)"
using assms
by(force simp add: substClosed_def Weak_Late_Cong_Pres.tauPres)

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PeqQ: "P \<simeq>\<^sup>s Q"

  shows "a<x>.P \<simeq>\<^sup>s a<x>.Q"
proof(auto simp add: substClosed_def)
  fix \<sigma> :: "(name \<times> name) list"
  {
    fix P Q a x \<sigma>
    assume "P \<simeq>\<^sup>s Q"
    then have "P[<\<sigma>>] \<simeq>\<^sup>s Q[<\<sigma>>]" by(rule partUnfold)
    then have "\<forall>y. (P[<\<sigma>>])[x::=y] \<simeq> (Q[<\<sigma>>])[x::=y]"
      apply(auto simp add: substClosed_def)
      by(erule_tac x="[(x, y)]" in allE) auto
    moreover assume "x \<sharp> \<sigma>"
    ultimately have "(a<x>.P)[<\<sigma>>] \<simeq> (a<x>.Q)[<\<sigma>>]" using weakBisimEqvt
      by(force intro: Weak_Late_Cong_Pres.inputPres)
  }
  note Goal = this

  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<sigma>"
    by(generate_fresh "name") auto
  from \<open>P \<simeq>\<^sup>s Q\<close> have "([(x, y)] \<bullet> P) \<simeq>\<^sup>s ([(x, y)] \<bullet> Q)" by(rule eqvtI)
  hence "(a<y>.([(x, y)] \<bullet> P))[<\<sigma>>] \<simeq> (a<y>.([(x, y)] \<bullet> Q))[<\<sigma>>]" using \<open>y \<sharp> \<sigma>\<close> by(rule Goal)
  moreover from \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" and "a<x>.Q = a<y>.([(x, y)] \<bullet> Q)"
    by(simp add: pi.alphaInput)+

  ultimately show "(a<x>.P)[<\<sigma>>] \<simeq> (a<x>.Q)[<\<sigma>>]" by simp
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "a{b}.P \<simeq>\<^sup>s a{b}.Q"
using assms
by(force simp add: substClosed_def Weak_Late_Cong_Pres.outputPres)

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<simeq>\<^sup>s Q"

  shows "[a\<frown>b]P \<simeq>\<^sup>s [a\<frown>b]Q"
using assms
by(force simp add: substClosed_def Weak_Late_Cong_Pres.matchPres)

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<oplus> R \<simeq>\<^sup>s Q \<oplus> R"
using assms
by(force simp add: substClosed_def Weak_Late_Cong_Pres.sumPres)

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<parallel> R \<simeq>\<^sup>s Q \<parallel> R"
using assms
by(force simp add: substClosed_def Weak_Late_Cong_Pres.parPres)

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PeqQ: "P \<simeq>\<^sup>s Q"
  
  shows "<\<nu>x>P \<simeq>\<^sup>s <\<nu>x>Q"
proof(auto simp add: substClosed_def)
  fix s::"(name \<times> name) list"

  have Goal: "\<And>P Q x s. \<lbrakk>P[<s>] \<leadsto><weakBisim> Q[<s>]; x \<sharp> s\<rbrakk> \<Longrightarrow> (<\<nu>x>P)[<s>] \<leadsto><weakBisim> (<\<nu>x>Q)[<s>]"
    by(force intro: Weak_Late_Step_Sim_Pres.resPres Weak_Late_Bisim_Pres.resPres Weak_Late_Bisim.eqvt)
  
  have "\<exists>c::name. c \<sharp> (P, Q, s)"  by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force simp add: fresh_prod)

  from PeqQ have "P[<([(x, c)] \<bullet> s)>] \<leadsto><weakBisim> Q[<([(x, c)] \<bullet> s)>]" and 
                 "Q[<([(x, c)] \<bullet> s)>] \<leadsto><weakBisim> P[<([(x, c)] \<bullet> s)>]"
    by(force simp add: congruenceSubstDef)+

  hence "([(x, c)] \<bullet> (P[<([(x, c)] \<bullet> s)>])) \<leadsto><weakBisim> ([(x, c)] \<bullet> (Q[<([(x, c)] \<bullet> s)>]))" and 
        "([(x, c)] \<bullet> (Q[<([(x, c)] \<bullet> s)>])) \<leadsto><weakBisim> ([(x, c)] \<bullet> (P[<([(x, c)] \<bullet> s)>]))"
    by(blast intro: Weak_Late_Step_Sim.eqvtI Weak_Late_Bisim.eqvt)+

  hence "([(x, c)] \<bullet> P)[<s>] \<leadsto><weakBisim> ([(x, c)] \<bullet> Q)[<s>]" and
        "([(x, c)] \<bullet> Q)[<s>] \<leadsto><weakBisim> ([(x, c)] \<bullet> P)[<s>]" by simp+

  with cFreshs have "(<\<nu>c>([(x, c)] \<bullet> P))[<s>] \<leadsto><weakBisim> (<\<nu>c>([(x, c)] \<bullet> Q))[<s>]" and
                    "(<\<nu>c>([(x, c)] \<bullet> Q))[<s>] \<leadsto><weakBisim> (<\<nu>c>([(x, c)] \<bullet> P))[<s>]"
    by(blast intro: Goal)+

  moreover from cFreshP cFreshQ have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" and "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)"
    by(simp add: alphaRes)+

  ultimately show "(<\<nu>x>P)[<s>] \<simeq> (<\<nu>x>Q)[<s>]"
    by(simp add: congruence_def)
qed

lemma congruenceBang:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "!P \<simeq>\<^sup>s !Q"
using assms
by(force simp add: substClosed_def intro: Weak_Late_Cong_Pres.congruenceBang)

end
