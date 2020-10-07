(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Bisim
  imports Strong_Early_Sim
begin

lemma monoAux: "A \<subseteq> B \<Longrightarrow> P \<leadsto>[A] Q \<longrightarrow> P \<leadsto>[B] Q"
by(auto intro: Strong_Early_Sim.monotonic)

coinductive_set bisim :: "(pi \<times> pi) set"
where
  step: "\<lbrakk>P \<leadsto>[bisim] Q; (Q, P) \<in> bisim\<rbrakk> \<Longrightarrow> (P, Q) \<in> bisim"
monos monoAux

abbreviation strongBisimJudge (infixr "\<sim>" 65) where "P \<sim> Q \<equiv> (P, Q) \<in> bisim"


lemma bisimCoinductAux[case_names bisim, case_conclusion StrongBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>[(X \<union> bisim)] Q \<and> (Q, P) \<in> bisim \<union> X"

  shows "P \<sim> Q"
proof -
  have aux: "X \<union> bisim = {(P, Q). (P, Q) \<in> X \<or> P \<sim> Q}" by blast

  from p show ?thesis
    by(coinduct, force dest: step simp add: aux)
qed

lemma bisimCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi
  
  assumes "(P, Q) \<in> X"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[(X \<union> bisim)] S"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<sim> Q"
using assms
by(coinduct rule: bisimCoinductAux) auto

lemma weak_coinduct[case_names bisim, case_conclusion StrongBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>[X] Q \<and> (Q, P) \<in> X"
 
  shows "P \<sim> Q"
using p
proof(coinduct rule: bisimCoinductAux)
  case (bisim P)
  from step[OF this] show ?case using Strong_Early_Sim.monotonic by blast
qed

lemma bisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi
  
  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>[X] Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<sim> Q"
using assms
by(coinduct rule: weak_coinduct) auto

lemma monotonic: "mono(\<lambda>p x1 x2.
        \<exists>P Q. x1 = P \<and>
              x2 = Q \<and> P \<leadsto>[{(xa, x). p xa x}] Q \<and> Q \<leadsto>[{(xa, x). p xa x}] P)"
apply(rule monoI)
by(auto intro: Strong_Early_Sim.monotonic)

lemma bisimE:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"
  
  shows "P \<leadsto>[bisim] Q"
  and   "Q \<sim> P"
using assms
by(auto intro: bisim.cases)

lemma bisimClosed[eqvt]:
  fixes P :: pi
  and   Q :: pi
  and   p :: "name prm"

  assumes "P \<sim> Q"

  shows "(p \<bullet> P) \<sim> (p \<bullet> Q)"
proof -
  let ?X = "{(p \<bullet> P, p \<bullet> Q) | (p::name prm) P Q. P \<sim> Q}"
  from assms have "(p \<bullet> P, p \<bullet> Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cSim P Q)
    moreover {
      fix P Q
      fix p::"name prm"
      assume "P \<leadsto>[bisim] Q"

      moreover have "bisim \<subseteq> ?X"
        by(auto, rule_tac x="[]" in exI) auto
      moreover have "eqvt ?X"
        by(auto simp add: eqvt_def pt2[OF pt_name_inst, THEN sym]) blast
      ultimately have "(p \<bullet> P) \<leadsto>[?X] (p \<bullet> Q)"
        by(rule Strong_Early_Sim.eqvtI)
    }
    ultimately show ?case by(blast dest: bisimE)
  next
    case(cSym P Q)
    thus ?case by(blast dest: bisimE)
  qed
qed

lemma eqvt[simp]:
  shows "eqvt bisim"
by(auto simp add: eqvt_def eqvts)

lemma reflexive:
  fixes P :: pi

  shows "P \<sim> P"
proof -
  have "(P, P) \<in> Id" by simp
  then show ?thesis
    by(coinduct rule: bisimWeakCoinduct) (auto intro: Strong_Early_Sim.reflexive)
qed

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes PBiSimQ: "P \<sim> Q"
  and     QBiSimR: "Q \<sim> R"

  shows "P \<sim> R"
proof -
  let ?X = "bisim O bisim"
  from assms have "(P, R) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cSim P Q)
    moreover {
      fix P Q R
      assume "P \<sim> Q" and "Q \<sim> R"
      hence "P \<leadsto>[bisim] Q" and "Q \<leadsto>[bisim] R"
        by(metis bisimE)+
      moreover from eqvt have "eqvt ?X" by(auto simp add: eqvtTrans)
      moreover have "bisim O bisim \<subseteq> ?X" by auto

      ultimately have "P \<leadsto>[?X] R"
        by(rule Strong_Early_Sim.transitive)
    }
    ultimately show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto dest: bisimE)
  qed
qed

end

