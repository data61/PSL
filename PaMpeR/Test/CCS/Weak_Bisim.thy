(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Bisim
  imports Weak_Sim Strong_Bisim_SC Struct_Cong
begin

lemma weakMonoCoinduct: "\<And>x y xa xb P Q.
                         x \<le> y \<Longrightarrow>
                         (Q \<leadsto>\<^sup>^<{(xb, xa). x xb xa}> P) \<longrightarrow>
                        (Q \<leadsto>\<^sup>^<{(xb, xa). y xb xa}> P)"
apply auto
apply(rule weakMonotonic)
by(auto dest: le_funE)

coinductive_set weakBisimulation :: "(ccs \<times> ccs) set"
where
  "\<lbrakk>P \<leadsto>\<^sup>^<weakBisimulation> Q; (Q, P) \<in> weakBisimulation\<rbrakk> \<Longrightarrow> (P, Q) \<in> weakBisimulation"
monos weakMonoCoinduct

abbreviation
  weakBisimJudge ("_ \<approx> _" [70, 70] 65) where "P \<approx> Q \<equiv> (P, Q) \<in> weakBisimulation"

lemma weakBisimulationCoinductAux[consumes 1]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(X \<union> weakBisimulation)> Q \<and> (Q, P) \<in> X"

  shows "P \<approx> Q"
proof -
  have "X \<union> weakBisimulation = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> weakBisimulation}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma weakBisimulationCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>\<^sup>^<(X \<union> weakBisimulation)> S"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<approx> Q"
proof -
  have "X \<union> weakBisimulation = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> weakBisimulation}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma weakBisimWeakCoinductAux[consumes 1]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<X> Q \<and> (Q, P) \<in> X" 

  shows "P \<approx> Q"
using assms
by(coinduct rule: weakBisimulationCoinductAux) (blast intro: weakMonotonic)

lemma weakBisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: "ccs"
  and   Q :: "ccs"
  and   X :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<X> Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
proof -
  have "X \<union> weakBisim = {(P, Q). (P, Q) \<in> X \<or> (P, Q) \<in> weakBisim}" by auto
  with assms show ?thesis
  by(coinduct rule: weakBisimulationCoinduct) (blast intro: weakMonotonic)+
qed

lemma weakBisimulationE:
  fixes P  :: "ccs"
  and   Q  :: "ccs"

  assumes "P \<approx> Q"

  shows "P \<leadsto>\<^sup>^<weakBisimulation> Q"
  and   "Q \<approx> P"
using assms
by(auto simp add: intro: weakBisimulation.cases)

lemma weakBisimulationI:
  fixes P :: "ccs"
  and   Q :: "ccs"

  assumes "P \<leadsto>\<^sup>^<weakBisimulation> Q"
  and     "Q \<approx> P"

  shows "P \<approx> Q"
using assms
by(auto intro: weakBisimulation.intros)

lemma reflexive: 
  fixes P :: ccs

  shows "P \<approx> P"
proof -
  have "(P, P) \<in> Id" by blast
  thus ?thesis
    by(coinduct rule: weakBisimulationCoinduct) (auto intro: Weak_Sim.reflexive)
qed

lemma symmetric: 
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<approx> Q"

  shows "Q \<approx> P"
using assms  
by(rule weakBisimulationE)

lemma transitive: 
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<approx> Q"
  and     "Q \<approx> R"

  shows "P \<approx> R"
proof -
  from assms have "(P, R) \<in> weakBisimulation O weakBisimulation" by auto
  thus ?thesis
  proof(coinduct rule: weakBisimulationCoinduct)
    case(cSim P R)
    from `(P, R) \<in> weakBisimulation O weakBisimulation`
    obtain Q where "P \<approx> Q" and "Q \<approx> R" by auto
    note `P \<approx> Q`
    moreover from `Q \<approx> R` have "Q \<leadsto>\<^sup>^<weakBisimulation> R" by(rule weakBisimulationE)
    moreover have "weakBisimulation O weakBisimulation \<subseteq> (weakBisimulation O weakBisimulation) \<union> weakBisimulation"
      by auto
    moreover note weakBisimulationE(1)
    ultimately show ?case by(rule Weak_Sim.transitive)
  next
    case(cSym P R)
    thus ?case by(blast dest: symmetric)
  qed
qed

lemma bisimWeakBisimulation:
  fixes P :: ccs
  and   Q :: ccs
  
  assumes "P \<sim> Q"

  shows "P \<approx> Q"
using assms
by(coinduct rule: weakBisimWeakCoinduct[where X=bisim])
  (auto dest: bisimE simWeakSim)

lemma structCongWeakBisimulation:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<equiv>\<^sub>s Q"

  shows "P \<approx> Q"
using assms

by(auto intro: bisimWeakBisimulation bisimStructCong)

lemma strongAppend:
  fixes P     :: ccs
  and   Q     :: ccs
  and   R     :: ccs
  and   Rel   :: "(ccs \<times> ccs) set"
  and   Rel'  :: "(ccs \<times> ccs) set"
  and   Rel'' :: "(ccs \<times> ccs) set"

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     QSimR: "Q \<leadsto>[Rel'] R"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"

  shows "P \<leadsto>\<^sup>^<Rel''> R"
using assms
by(simp add: weakSimulation_def simulation_def) blast

lemma weakBisimWeakUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(weakBisimulation O X O bisim)> Q"
  and rSym: "\<And> P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
proof -
  let ?X = "weakBisimulation O X O weakBisimulation"
  let ?Y = "weakBisimulation O X O bisim"
  from `(P, Q) \<in> X` have "(P, Q) \<in> ?X" by(blast intro: Strong_Bisim.reflexive reflexive)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cSim P Q)
    {
      fix P P' Q' Q
      assume "P \<approx> P'" and "(P', Q') \<in> X" and "Q' \<approx> Q"
      from `(P', Q') \<in> X` have "(P', Q') \<in> ?Y" by(blast intro: reflexive Strong_Bisim.reflexive)
      moreover from `Q' \<approx> Q` have "Q' \<leadsto>\<^sup>^<weakBisimulation> Q" by(rule weakBisimulationE)
      moreover have "?Y O weakBisimulation \<subseteq> ?X" by(blast dest: bisimWeakBisimulation transitive)
      moreover {
        fix P Q
        assume "(P, Q) \<in> ?Y"
        then obtain P' Q' where "P \<approx> P'" and "(P', Q') \<in> X" and "Q' \<sim> Q" by auto
        from `(P', Q') \<in> X` have "P' \<leadsto>\<^sup>^<?Y> Q'" by(rule rSim)
        moreover from `Q' \<sim> Q` have "Q' \<leadsto>[bisim] Q" by(rule bisimE)
        moreover have "?Y O bisim \<subseteq> ?Y" by(auto dest: Strong_Bisim.transitive)
        ultimately have "P' \<leadsto>\<^sup>^<?Y> Q" by(rule strongAppend)
        moreover note `P \<approx> P'`
        moreover have "weakBisimulation O ?Y \<subseteq> ?Y" by(blast dest: transitive)
        ultimately have "P \<leadsto>\<^sup>^<?Y> Q" using weakBisimulationE(1)
          by(rule_tac Weak_Sim.transitive)
      }
      ultimately have "P' \<leadsto>\<^sup>^<?X> Q" by(rule Weak_Sim.transitive)
      moreover note `P \<approx> P'`
      moreover have "weakBisimulation O ?X \<subseteq> ?X" by(blast dest: transitive)
      ultimately have "P \<leadsto>\<^sup>^<?X> Q" using weakBisimulationE(1)
        by(rule_tac Weak_Sim.transitive)
    }
    with `(P, Q) \<in> ?X` show ?case by auto
  next
    case(cSym P Q)
    thus ?case 
      apply auto
      by(blast dest: bisimE rSym weakBisimulationE)
  qed
qed

lemma weakBisimUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto>\<^sup>^<(weakBisimulation O (X \<union> weakBisimulation) O bisim)> S"
  and rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<approx> Q"
proof -
  from p have "(P, Q) \<in> X \<union> weakBisimulation" by simp
  thus ?thesis
    apply(coinduct rule: weakBisimWeakUpto)
    apply(auto dest: rSim rSym weakBisimulationE)
    apply(rule weakMonotonic)
    apply(blast dest: weakBisimulationE)
    apply(auto simp add: relcomp_unfold)
    by(metis reflexive Strong_Bisim.reflexive transitive)
qed

end
