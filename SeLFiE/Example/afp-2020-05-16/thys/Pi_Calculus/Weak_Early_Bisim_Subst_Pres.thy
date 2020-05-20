(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Bisim_Subst_Pres
  imports Weak_Early_Bisim_Subst Weak_Early_Bisim_Pres
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<approx>\<^sup>s Q"

  shows "\<tau>.(P) \<approx>\<^sup>s \<tau>.(Q)"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.tauPres)

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PeqQ: "P \<approx>\<^sup>s Q"

  shows "a<x>.P \<approx>\<^sup>s a<x>.Q"
proof(auto simp add: substClosed_def)
  fix \<sigma> :: "(name \<times> name) list"
  {
    fix P Q a x \<sigma>
    assume "P \<approx>\<^sup>s Q"
    then have "P[<\<sigma>>] \<approx>\<^sup>s Q[<\<sigma>>]" by(rule partUnfold)
    then have "\<forall>y. (P[<\<sigma>>])[x::=y] \<approx> (Q[<\<sigma>>])[x::=y]"
      apply(auto simp add: substClosed_def)
      by(erule_tac x="[(x, y)]" in allE) auto
    moreover assume "x \<sharp> \<sigma>"
    ultimately have "(a<x>.P)[<\<sigma>>] \<approx> (a<x>.Q)[<\<sigma>>]" 
      by(force intro: Weak_Early_Bisim_Pres.inputPres)
  }
  note Goal = this

  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<sigma>"
    by(generate_fresh "name") auto
  from \<open>P \<approx>\<^sup>s Q\<close> have "([(x, y)] \<bullet> P) \<approx>\<^sup>s ([(x, y)] \<bullet> Q)" by(rule eqvts)
  hence "(a<y>.([(x, y)] \<bullet> P))[<\<sigma>>] \<approx> (a<y>.([(x, y)] \<bullet> Q))[<\<sigma>>]" using \<open>y \<sharp> \<sigma>\<close> by(rule Goal)
  moreover from \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" and "a<x>.Q = a<y>.([(x, y)] \<bullet> Q)"
    by(simp add: alphaInput)+

  ultimately show "(a<x>.P)[<\<sigma>>] \<approx> (a<x>.Q)[<\<sigma>>]" by simp  
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<approx>\<^sup>s Q"

  shows "a{b}.P \<approx>\<^sup>s a{b}.Q"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.outputPres)

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx>\<^sup>s Q"

  shows "[a\<frown>b]P \<approx>\<^sup>s [a\<frown>b]Q"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.matchPres)

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<approx>\<^sup>s Q"

  shows "[a\<noteq>b]P \<approx>\<^sup>s [a\<noteq>b]Q"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.mismatchPres)

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<approx>\<^sup>s Q"

  shows "P \<parallel> R \<approx>\<^sup>s Q \<parallel> R"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.parPres)

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes PeqQ: "P \<approx>\<^sup>s Q"
  
  shows "<\<nu>x>P \<approx>\<^sup>s <\<nu>x>Q"
proof(auto simp add: substClosed_def)
  fix s::"(name \<times> name) list"

  have Res: "\<And>P Q x s. \<lbrakk>P[<s>] \<approx> Q[<s>]; x \<sharp> s\<rbrakk> \<Longrightarrow> (<\<nu>x>P)[<s>] \<approx> (<\<nu>x>Q)[<s>]"
    by(force intro: Weak_Early_Bisim_Pres.resPres)

  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cFreshs: "c \<sharp> s"
    by(force intro: name_exists_fresh[of "(P, Q, s)"])

  from PeqQ have "P[<([(x, c)] \<bullet> s)>] \<approx> Q[<([(x, c)] \<bullet> s)>]" by(simp add: substClosed_def)
  hence "([(x, c)] \<bullet> P[<([(x, c)] \<bullet> s)>]) \<approx> ([(x, c)] \<bullet> Q[<([(x, c)] \<bullet> s)>])" by(rule Weak_Early_Bisim.eqvtI)
  hence "([(x, c)] \<bullet> P)[<s>] \<approx> ([(x, c)] \<bullet> Q)[<s>]" by simp
  hence "(<\<nu>c>([(x, c)] \<bullet> P))[<s>] \<approx> (<\<nu>c>([(x, c)] \<bullet> Q))[<s>]" using cFreshs by(rule Res)

  moreover from cFreshP cFreshQ have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" and "<\<nu>x>Q = <\<nu>c>([(x, c)] \<bullet> Q)"
    by(simp add: alphaRes)+

  ultimately show "(<\<nu>x>P)[<s>] \<approx> (<\<nu>x>Q)[<s>]" by simp
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<approx>\<^sup>s Q"

  shows "!P \<approx>\<^sup>s !Q"
using assms
by(force simp add: substClosed_def intro: Weak_Early_Bisim_Pres.bangPres)

end
