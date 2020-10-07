(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Bisim_Subst
  imports Weak_Late_Bisim Strong_Late_Bisim_Subst
begin

consts weakBisimSubst :: "(pi \<times> pi) set"
abbreviation
  weakBisimSubstJudge (infixr "\<approx>\<^sup>s" 65) where "P \<approx>\<^sup>s Q \<equiv> (P, Q) \<in> (substClosed weakBisim)"

lemma congBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx>\<^sup>s Q"

  shows "P \<approx> Q"
proof -
  from assms substClosedSubset show ?thesis
    by blast
qed

lemma strongBisimWeakBisim:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<sim>\<^sup>s Q"

  shows "P \<approx>\<^sup>s Q"
using assms
by(auto simp add: substClosed_def intro: strongBisimWeakBisim)

lemma eqvt:
  shows "eqvt (substClosed weakBisim)"
by(rule eqvtSubstClosed[OF Weak_Late_Bisim.eqvt])

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<approx>\<^sup>s Q"

  shows "(perm \<bullet> P) \<approx>\<^sup>s (perm \<bullet> Q)"
using assms
by(rule_tac eqvtRelI[OF eqvt])

lemma reflexive:
  fixes P :: pi
  
  shows "P \<approx>\<^sup>s P"
by(force simp add: substClosed_def intro: Weak_Late_Bisim.reflexive)

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<approx>\<^sup>s Q"
  
  shows "Q \<approx>\<^sup>s P"
using assms
by(force simp add: substClosed_def intro: Weak_Late_Bisim.symmetric)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<approx>\<^sup>s Q"
  and     "Q \<approx>\<^sup>s R"
  
  shows "P \<approx>\<^sup>s R"
using assms
by(force simp add: substClosed_def intro: Weak_Late_Bisim.transitive)


lemma partUnfold:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<approx>\<^sup>s Q"

  shows "P[<s>] \<approx>\<^sup>s Q[<s>]"
using assms
proof(auto simp add: substClosed_def)
  fix s'
  assume "\<forall>s. P[<s>] \<approx> Q[<s>]"
  hence "P[<(s@s')>] \<approx> Q[<(s@s')>]" by blast
  moreover have "P[<(s@s')>] = (P[<s>])[<s'>]"
    by(induct s', auto)
  moreover have "Q[<(s@s')>] = (Q[<s>])[<s'>]"
    by(induct s', auto)
  
  ultimately show "(P[<s>])[<s'>] \<approx> (Q[<s>])[<s'>]"
    by simp
qed
  
end
