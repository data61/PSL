(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Bisim
  imports Strong_Sim
begin

lemma monotonic:
  fixes P :: ccs
  and   A :: "(ccs \<times> ccs) set"
  and   Q :: ccs
  and   B :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>[A] Q"
  and     "A \<subseteq> B"

  shows "P \<leadsto>[B] Q"
using assms
by(fastforce simp add: simulation_def)

lemma monoCoinduct: "\<And>x y xa xb P Q.
                      x \<le> y \<Longrightarrow>
                      (Q \<leadsto>[{(xb, xa). x xb xa}] P) \<longrightarrow>
                     (Q \<leadsto>[{(xb, xa). y xb xa}] P)"
apply auto
apply(rule monotonic)
by(auto dest: le_funE)

coinductive_set bisim :: "(ccs \<times> ccs) set"
where
  "\<lbrakk>P \<leadsto>[bisim] Q; (Q, P) \<in> bisim\<rbrakk> \<Longrightarrow> (P, Q) \<in> bisim"
monos monoCoinduct

abbreviation
  bisimJudge ("_ \<sim> _" [70, 70] 65) where "P \<sim> Q \<equiv> (P, Q) \<in> bisim"

lemma bisimCoinductAux[consumes 1]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>[(X \<union> bisim)] Q \<and> (Q, P) \<in> X"

  shows "P \<sim> Q"
proof -
  have "X \<union> bisim = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisimCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[(X \<union> bisim)] S"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<sim> Q"
proof -
  have "X \<union> bisim = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisimWeakCoinductAux[consumes 1]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[X] S \<and> (S, R) \<in> X" 

  shows "P \<sim> Q"
using assms
by(coinduct rule: bisimCoinductAux) (blast intro: monotonic)

lemma bisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>[X] Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<sim> Q"
proof -
  have "X \<union> bisim = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> bisim}" by auto
  with assms show ?thesis
  by(coinduct rule: bisimCoinduct) (blast intro: monotonic)+
qed

lemma bisimE:
  fixes P  :: "ccs"
  and   Q  :: "ccs"

  assumes "P \<sim> Q"

  shows "P \<leadsto>[bisim] Q"
  and   "Q \<sim> P"
using assms
by(auto simp add: intro: bisim.cases)

lemma bisimI:
  fixes P :: "ccs"
  and   Q :: "ccs"

  assumes "P \<leadsto>[bisim] Q"
  and     "Q \<sim> P"

  shows "P \<sim> Q"
using assms
by(auto intro: bisim.intros)

lemma reflexive: 
  fixes P :: ccs

  shows "P \<sim> P"
proof -
  have "(P, P) \<in> Id" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: reflexive)
qed

lemma symmetric: 
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<sim> Q"

  shows "Q \<sim> P"
using assms  
by(rule bisimE)

lemma transitive: 
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<sim> Q"
  and     "Q \<sim> R"

  shows "P \<sim> R"
proof -
  from assms have "(P, R) \<in> bisim O bisim" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: transitive dest: bisimE)
qed

lemma bisimTransCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: ccs
  and   Q :: ccs

  assumes "(P, Q) \<in> X"
  and     rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>[(bisim O X O bisim)] S"
  and     rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<sim> Q"
proof -
  from `(P, Q) \<in> X` have "(P, Q) \<in> bisim O X O bisim"
    by(auto intro: reflexive)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cSim P Q)
    from `(P, Q) \<in> bisim O X O bisim`
    obtain R S where "P \<sim> R" and "(R, S) \<in> X" and "S \<sim> Q"
      by auto
    from `P \<sim> R` have "P \<leadsto>[bisim] R" by(rule bisimE)
    moreover from `(R, S) \<in> X` have "R \<leadsto>[(bisim O X O bisim)] S"
      by(rule rSim)
    moreover have "bisim O (bisim O X O bisim) \<subseteq> bisim O X O bisim"
      by(auto intro: transitive)
    ultimately have "P \<leadsto>[(bisim O X O bisim)] S"
      by(rule Strong_Sim.transitive)
    moreover from `S \<sim> Q` have "S \<leadsto>[bisim] Q" by(rule bisimE)
    moreover have "(bisim O X O bisim) O bisim \<subseteq> bisim O X O bisim"
      by(auto intro: transitive)
    ultimately show ?case by(rule Strong_Sim.transitive)
  next
    case(cSym P Q)
    thus ?case by(auto dest: symmetric rSym)
  qed
qed

end
