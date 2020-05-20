(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Cong_Subst
  imports Weak_Early_Cong Weak_Early_Bisim_Subst Strong_Early_Bisim_Subst
begin

consts congruenceSubst :: "(pi \<times> pi) set"

definition weakCongruenceSubst (infixr "\<simeq>\<^sup>s" 65) where "P \<simeq>\<^sup>s Q \<equiv> \<forall>\<sigma>. P[<\<sigma>>] \<simeq> Q[<\<sigma>>]"

lemma unfoldE:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq>\<^sup>s Q"

  shows "P[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q[<s>]"
  and   "Q[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P[<s>]"
proof -
  from assms show "P[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q[<s>]" by(simp add: weakCongruenceSubst_def weakCongruence_def)
next
  from assms show "Q[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P[<s>]" by(simp add: weakCongruenceSubst_def weakCongruence_def)
qed

lemma unfoldI:
  fixes P :: pi
  and   Q :: pi

  assumes "\<And>s. P[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q[<s>]"
  and     "\<And>s. Q[<s>] \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P[<s>]"

  shows "P \<simeq>\<^sup>s Q"
using assms
by(simp add: weakCongruenceSubst_def weakCongruence_def)

lemma weakCongWeakEq:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<simeq> Q"
using assms
apply(simp add: weakCongruenceSubst_def weakCongruence_def)
apply(erule_tac x="[]" in allE)
by auto

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   p :: "name prm"

  assumes "P \<simeq>\<^sup>s Q"

  shows "(p \<bullet> P) \<simeq>\<^sup>s (p \<bullet> Q)"
proof(simp add: weakCongruenceSubst_def, rule allI)
  fix s
  from assms have "P[<(rev p \<bullet> s)>] \<simeq> Q[<(rev p \<bullet> s)>]" by(auto simp add: weakCongruenceSubst_def)
  thus "(p \<bullet> P)[<s>] \<simeq> (p \<bullet> Q)[<s>]" by(drule_tac p=p in Weak_Early_Cong.eqvtI) (simp add: eqvts name_per_rev)
qed

lemma strongEqWeakCong:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<sim>\<^sup>s Q"

  shows "P \<simeq>\<^sup>s Q"
using assms
by(auto intro: strongBisimWeakCong simp add: substClosed_def weakCongruenceSubst_def)

lemma congSubstBisimSubst:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<approx>\<^sup>s Q"
using assms
by(auto intro: congruenceWeakBisim simp add: substClosed_def weakCongruenceSubst_def)

lemma reflexive:
  fixes P :: pi
  
  shows "P \<simeq>\<^sup>s P"
proof -
  from Weak_Early_Bisim.reflexive have "\<And>P. P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"
    by(blast intro: Weak_Early_Step_Sim.reflexive)
  thus ?thesis
    by(force simp add: weakCongruenceSubst_def weakCongruence_def)
qed

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"
  
  shows "Q \<simeq>\<^sup>s P"
using assms by(auto simp add: weakCongruenceSubst_def weakCongruence_def)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<simeq>\<^sup>s Q"
  and     "Q \<simeq>\<^sup>s R"
  
  shows "P \<simeq>\<^sup>s R"
using assms by(auto simp add: weakCongruenceSubst_def intro: Weak_Early_Cong.transitive)

lemma partUnfold:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq>\<^sup>s Q"

  shows "P[<s>] \<simeq>\<^sup>s Q[<s>]"
using assms
proof(auto simp add: weakCongruenceSubst_def)
  fix s'
  assume "\<forall>s. P[<s>] \<simeq> Q[<s>]"
  hence "P[<(s@s')>] \<simeq> Q[<(s@s')>]" by blast
  moreover have "P[<(s@s')>] = (P[<s>])[<s'>]"
    by(induct s', auto)
  moreover have "Q[<(s@s')>] = (Q[<s>])[<s'>]"
    by(induct s', auto)
  
  ultimately show "(P[<s>])[<s'>] \<simeq> (Q[<s>])[<s'>]"
    by simp
qed

end
