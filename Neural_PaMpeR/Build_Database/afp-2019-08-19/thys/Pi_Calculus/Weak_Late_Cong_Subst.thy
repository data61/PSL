(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Cong_Subst
  imports Weak_Late_Cong Weak_Late_Bisim_Subst Strong_Late_Bisim_Subst
begin

definition congruenceSubst :: "pi \<Rightarrow> pi\<Rightarrow> bool" (infixr "\<simeq>\<^sup>s" 65) where
  "P \<simeq>\<^sup>s Q \<equiv> (P, Q) \<in> (substClosed congruence)"

lemmas congruenceSubstDef = congruenceSubst_def congruence_def substClosed_def

lemma unfoldE:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq>\<^sup>s Q"

  shows "P[<s>] \<leadsto><weakBisim> Q[<s>]"
  and   "Q[<s>] \<leadsto><weakBisim> P[<s>]"
proof -
  from assms show "P[<s>] \<leadsto><weakBisim> Q[<s>]" by(force simp add: congruenceSubstDef)
next
  from assms show "Q[<s>] \<leadsto><weakBisim> P[<s>]" by(force simp add: congruenceSubstDef)
qed

lemma unfoldI:
  fixes P :: pi
  and   Q :: pi

  assumes "\<forall>s. P[<s>] \<leadsto><weakBisim> Q[<s>] \<and> Q[<s>] \<leadsto><weakBisim> P[<s>]"

  shows "P \<simeq>\<^sup>s Q"
proof -
  from assms show ?thesis by(force simp add: congruenceSubstDef)
qed

lemma weakEqSubset:
  shows "substClosed congruence \<subseteq> weakBisim"
proof(auto simp add: substClosed_def)
  fix P Q
  assume "\<forall>s. P[<s>] \<simeq> Q[<s>]"
  hence "P[<[]>] \<simeq> Q[<[]>]" by blast
  thus "P \<approx> Q"
    by(force dest: congruenceWeakBisim intro: Weak_Late_Bisim.unfoldI)
qed


lemma weakCongWeakEq:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<simeq> Q"
using assms
apply(auto simp add: substClosed_def congruenceSubst_def)
apply(erule_tac x="[]" in allE)
by auto

lemma eqvt:
  shows "eqvt (substClosed congruence)"
by(rule eqvtSubstClosed[OF Weak_Late_Cong.eqvt])

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<simeq>\<^sup>s Q"

  shows "(perm \<bullet> P) \<simeq>\<^sup>s (perm \<bullet> Q)"
using assms
by(simp add: congruenceSubst_def) (rule eqvtRelI[OF eqvt])

lemma strongEqWeakCong:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<sim>\<^sup>s Q"

  shows "P \<simeq>\<^sup>s Q"
using assms
by(force intro: strongBisimWeakEq simp add: substClosed_def congruenceSubst_def)

lemma congSubstBisimSubst:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"

  shows "P \<approx>\<^sup>s Q"
using assms
by(force simp add: congruenceSubst_def substClosed_def intro: congruenceWeakBisim)


lemma reflexive:
  fixes P :: pi
  
  shows "P \<simeq>\<^sup>s P"
proof -
  from Weak_Late_Bisim.reflexive have "\<And>P. P \<leadsto><weakBisim> P"
    by(blast intro: Weak_Late_Step_Sim.reflexive)
  thus ?thesis
    by(force simp add: congruenceSubstDef)
qed

lemma symetric:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<simeq>\<^sup>s Q"
  
  shows "Q \<simeq>\<^sup>s P"
using assms
by(force simp add: congruenceSubstDef)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<simeq>\<^sup>s Q"
  and     "Q \<simeq>\<^sup>s R"
  
  shows "P \<simeq>\<^sup>s R"
using assms
by(force simp add: congruenceSubst_def substClosed_def intro: Weak_Late_Cong.transitive)

lemma partUnfold:
  fixes P :: pi
  and   Q :: pi
  and   s :: "(name \<times> name) list"

  assumes "P \<simeq>\<^sup>s Q"

  shows "P[<s>] \<simeq>\<^sup>s Q[<s>]"
using assms
proof(auto simp add: congruenceSubst_def substClosed_def)
  fix s'
  assume "\<forall>s. (P[<s>], Q[<s>]) \<in> congruence"
  hence "(P[<(s@s')>], Q[<(s@s')>]) \<in> congruence" by blast
  moreover have "P[<(s@s')>] = (P[<s>])[<s'>]"
    by(induct s', auto)
  moreover have "Q[<(s@s')>] = (Q[<s>])[<s'>]"
    by(induct s', auto)
  
  ultimately show "((P[<s>])[<s'>], (Q[<s>])[<s'>]) \<in> congruence"
    by simp
qed

end
