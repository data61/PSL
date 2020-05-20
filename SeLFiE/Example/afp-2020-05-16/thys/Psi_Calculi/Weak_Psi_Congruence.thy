(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Psi_Congruence
  imports Weak_Cong_Simulation Weak_Bisimulation
begin

context env begin

definition weakPsiCongruence :: "'b \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> ('a, 'b, 'c) psi \<Rightarrow> bool" ("_ \<rhd> _ \<doteq> _" [70, 70, 70] 65)
where 
  "\<Psi> \<rhd> P \<doteq> Q \<equiv> \<Psi> \<rhd> P \<approx> Q \<and> \<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q \<and> \<Psi> \<rhd> Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"

abbreviation
  weakPsiCongNilJudge ("_ \<doteq> _" [70, 70] 65) where "P \<doteq> Q \<equiv> \<one> \<rhd> P \<doteq> Q"

lemma weakPsiCongSym:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> Q \<doteq> P"
using assms
by(auto simp add: weakPsiCongruence_def weakBisimE)

lemma weakPsiCongE:
  fixes \<Psi>   :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>'  :: 'b


  assumes "\<Psi> \<rhd> P \<doteq> Q"

  shows "\<Psi> \<rhd> P \<approx> Q"
  and   "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
  and   "\<Psi> \<rhd> Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"
using assms
by(auto simp add: weakPsiCongruence_def)

lemma weakPsiCongI[case_names cWeakBisim cSimLeft cSimRight]:
  fixes \<Psi>  :: 'b
  and   P   :: "('a, 'b, 'c) psi"
  and   Q   :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<approx> Q"
  and     "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q"
  and     "\<Psi> \<rhd> Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> P"

  shows "\<Psi> \<rhd> P \<doteq> Q"
using assms
by(auto simp add: weakPsiCongruence_def)

lemma weakPsiCongSymI[consumes 1, case_names cSym cWeakBisim cSim]:
  fixes \<Psi>  :: 'b
  and   P   :: "'d::fs_name"
  and   Q   :: 'd
  and   \<Psi>' :: 'b

  assumes "Prop P Q"
  and     "\<And>P Q. Prop P Q \<Longrightarrow> Prop Q P"

  and     "\<And>P Q. Prop P Q \<Longrightarrow> \<Psi> \<rhd> (C P) \<approx> (C Q)"

  and     "\<And>P Q. Prop P Q \<Longrightarrow> \<Psi> \<rhd> (C P) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (C Q)"

  shows "\<Psi> \<rhd> (C P) \<doteq> (C Q)"
using assms
by(rule_tac weakPsiCongI) auto

lemma weakPsiCongSym2[consumes 1, case_names cWeakBisim cSim]:
  fixes \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "\<Psi> \<rhd> P \<doteq> Q"

  and     "\<And>P Q. \<Psi> \<rhd> P \<doteq> Q \<Longrightarrow> \<Psi> \<rhd> (C P) \<approx> (C Q)"

  and     "\<And>P Q. \<Psi> \<rhd> P \<doteq> Q \<Longrightarrow> \<Psi> \<rhd> (C P) \<leadsto>\<guillemotleft>weakBisim\<guillemotright> (C Q)"

  shows "\<Psi> \<rhd> (C P) \<doteq> (C Q)"
using assms
apply(rule_tac weakPsiCongSymI[where C=C])
apply assumption
by(auto simp add: weakPsiCongruence_def dest: weakBisimE)

lemma statEqWeakCong:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b
  
  assumes "\<Psi> \<rhd> P \<doteq> Q"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<doteq> Q"
proof -
  let ?Prop = "\<lambda>P Q. \<Psi> \<rhd> P \<doteq> Q \<and> \<Psi> \<simeq> \<Psi>'"
  from assms have "?Prop P Q" by auto
  thus ?thesis
  proof(induct rule: weakPsiCongSymI)
    case(cSym P Q)
    thus ?case by(blast dest: weakPsiCongSym)
  next
    case(cSim P Q)
    from \<open>\<Psi> \<rhd> P \<doteq> Q \<and> \<Psi> \<simeq> \<Psi>'\<close> have "\<Psi> \<rhd> P \<doteq> Q" and "\<Psi> \<simeq> \<Psi>'" by simp+
    from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(rule weakPsiCongE)
    with \<open>\<Psi> \<simeq> \<Psi>'\<close> show ?case using statEqWeakBisim
      by(rule_tac weakCongSimStatEq) auto
  next
    case(cWeakBisim P Q)
    from \<open>\<Psi> \<rhd> P \<doteq> Q \<and> \<Psi> \<simeq> \<Psi>'\<close>
    have "\<Psi> \<rhd> P \<approx> Q" and "\<Psi> \<simeq> \<Psi>'" by(auto dest: weakPsiCongE)
    thus ?case by(rule statEqWeakBisim)
  qed
qed

lemma weakPsiCongReflexive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"


  shows "\<Psi> \<rhd> P \<doteq> P"
by(fastforce intro: weakPsiCongI weakCongSimReflexive weakBisimReflexive)

lemma weakPsiCongClosed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"
  
  assumes "\<Psi> \<rhd> P \<doteq> Q"

  shows "(p \<bullet> \<Psi>) \<rhd>  (p \<bullet> P) \<doteq> (p \<bullet> Q)"
using assms
proof(induct rule: weakPsiCongSymI)
  case(cSym P Q)
  thus ?case by(rule weakPsiCongSym)
next
  case(cSim P Q)
  from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(rule weakPsiCongE)
  thus ?case by(drule_tac p=p in weakCongSimClosed(1)[OF weakBisimEqvt]) (simp add: eqvts)
next
  case(cWeakBisim P Q)
  from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<approx> Q" by(rule weakPsiCongE)
  thus ?case by(rule weakBisimClosed)
qed

lemma weakPsiCongTransitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<doteq> Q"
  and     "\<Psi> \<rhd> Q \<doteq> R"

  shows "\<Psi> \<rhd> P \<doteq> R"
proof -
  from assms have "\<Psi> \<rhd> P \<doteq> Q \<and> \<Psi> \<rhd> Q \<doteq> R"  by auto
  thus ?thesis
  proof(induct rule: weakPsiCongSymI)
    case(cSym P R)
    thus ?case by(auto dest: weakPsiCongSym)
  next
    case(cSim P R)
    hence "\<Psi> \<rhd> P \<doteq> Q" and  "\<Psi> \<rhd> Q \<doteq> R"  by auto
    moreover from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<approx> Q" by(metis weakBisimE weakPsiCongE)
    moreover from \<open>\<Psi> \<rhd> P \<doteq> Q\<close> have "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" by(rule weakPsiCongE)
    moreover from \<open>\<Psi> \<rhd> Q \<doteq> R\<close> have "\<Psi> \<rhd> Q \<leadsto>\<guillemotleft>weakBisim\<guillemotright> R" by(rule weakPsiCongE)
    moreover have "{(\<Psi>, P, R) | \<Psi> P R. \<exists>Q. \<Psi> \<rhd> P \<approx> Q \<and> \<Psi> \<rhd> Q \<approx> R} \<subseteq> weakBisim"
      by(auto dest: weakBisimTransitive)
    ultimately show ?case using weakBisimE(2) by(rule_tac weakCongSimTransitive)
  next
    case(cWeakBisim P R)
    thus ?case by(auto dest: weakBisimTransitive weakPsiCongE)
  qed
qed

lemma strongBisimWeakPsiCong:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"

  shows "\<Psi> \<rhd> P \<doteq> Q"
using assms
proof(induct rule: weakPsiCongSymI)
  case(cSym P Q)
  from \<open>\<Psi> \<rhd> P \<sim> Q\<close> show ?case by(rule bisimE)
next
  case(cSim P Q)
  from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> P \<leadsto>[bisim] Q" by(rule bisimE)
  thus "\<Psi> \<rhd> P \<leadsto>\<guillemotleft>weakBisim\<guillemotright> Q" using strongBisimWeakBisim
    by(rule_tac strongSimWeakCongSim) auto
next
  case(cWeakBisim P Q)
  thus ?case by(rule strongBisimWeakBisim)
qed

lemma structCongWeakPsiCong:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<doteq> Q"
using assms
by(metis structCongBisim strongBisimWeakPsiCong)

end

end



