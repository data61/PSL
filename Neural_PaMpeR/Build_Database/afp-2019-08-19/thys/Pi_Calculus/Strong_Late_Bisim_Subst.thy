(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Bisim_Subst
  imports Strong_Late_Bisim
begin

abbreviation
  StrongEqJudge (infixr "\<sim>\<^sup>s" 65) where "P \<sim>\<^sup>s Q \<equiv> (P, Q) \<in> (substClosed bisim)"


lemma congBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim>\<^sup>s Q"

  shows "P \<sim> Q"
using assms substClosedSubset by blast

lemma eqvt:
  shows "eqvt (substClosed bisim)"
by(rule eqvtSubstClosed[OF Strong_Late_Bisim.bisimEqvt])

lemma eqClosed:
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
by(force simp add: substClosed_def intro: Strong_Late_Bisim.reflexive)

lemma symmetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<sim>\<^sup>s Q"
  
  shows "Q \<sim>\<^sup>s P"
using assms
by(force simp add: substClosed_def intro: Strong_Late_Bisim.symmetric)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<sim>\<^sup>s Q"
  and     "Q \<sim>\<^sup>s R"
  
  shows "P \<sim>\<^sup>s R"
using assms
by(force simp add: substClosed_def intro: Strong_Late_Bisim.transitive)

end
