(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Bisim_Subst
  imports Strong_Early_Bisim
begin

abbreviation StrongCongEarlyJudge (infixr "\<sim>\<^sup>s" 65) where   "P \<sim>\<^sup>s Q \<equiv> (P, Q) \<in> (substClosed bisim)"

lemma congBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim>\<^sup>s Q"

  shows "P \<sim> Q"
using assms substClosedSubset by blast

lemma eqvt:
  shows "eqvt (substClosed bisim)"
by(rule eqvtSubstClosed[OF Strong_Early_Bisim.eqvt])

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<sim>\<^sup>s Q"

  shows "(perm \<bullet> P) \<sim>\<^sup>s (perm \<bullet> Q)"
using assms
by(rule eqvtRelI[OF eqvt])

lemma reflexive:
  fixes P :: pi
  
  shows "P \<sim>\<^sup>s P"
by(force simp add: substClosed_def intro: Strong_Early_Bisim.reflexive)

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<sim>\<^sup>s Q"
  
  shows "Q \<sim>\<^sup>s P"
using assms
by(force simp add: substClosed_def intro: Strong_Early_Bisim.bisimE)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<sim>\<^sup>s Q"
  and     "Q \<sim>\<^sup>s R"
  
  shows "P \<sim>\<^sup>s R"
using assms
by(force simp add: substClosed_def intro: Strong_Early_Bisim.transitive)

lemma partUnfold:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<sim>\<^sup>s Q"

  shows "P[<s>] \<sim>\<^sup>s Q[<s>]"
using assms
proof(auto simp add: substClosed_def)
  fix s'
  assume "\<forall>s. P[<s>] \<sim> Q[<s>]"
  hence "P[<(s@s')>] \<sim> Q[<(s@s')>]" by blast
  moreover have "P[<(s@s')>] = (P[<s>])[<s'>]"
    by(induct s', auto)
  moreover have "Q[<(s@s')>] = (Q[<s>])[<s'>]"
    by(induct s', auto)
  
  ultimately show "(P[<s>])[<s'>] \<sim> (Q[<s>])[<s'>]"
    by simp
qed
  
end
