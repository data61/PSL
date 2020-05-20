(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Bisim
  imports Weak_Early_Sim Strong_Early_Bisim
begin

lemma monoAux: "A \<subseteq> B \<Longrightarrow> P \<leadsto><A> Q \<longrightarrow> P \<leadsto><B> Q"
by(auto intro: Weak_Early_Sim.monotonic)

coinductive_set weakBisim :: "(pi \<times> pi) set"
where
  step: "\<lbrakk>P \<leadsto><weakBisim> Q; (Q, P) \<in> weakBisim\<rbrakk> \<Longrightarrow> (P, Q) \<in> weakBisim"
monos monoAux

abbreviation weakEarlyBisimJudge (infixr "\<approx>" 65) where "P \<approx> Q \<equiv> (P, Q) \<in> weakBisim"

lemma weakBisimCoinductAux[case_names weakBisim, case_conclusion weakBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto><(X \<union> weakBisim)> Q \<and> (Q, P) \<in> X \<union> weakBisim"

  shows "P \<approx> Q"
proof -
  have aux: "X \<union> weakBisim = {(P, Q). (P, Q) \<in> X \<or> P \<approx> Q}" by blast

  from p show ?thesis
    by(coinduct, force dest: step simp add: aux)
qed

lemma weakBisimWeakCoinductAux[case_names weakBisim, case_conclusion weakBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto><X> Q \<and> (Q, P) \<in> X"

  shows "P \<approx> Q"
using p
proof(coinduct rule: weakBisimCoinductAux)
  case (weakBisim P)
  from step[OF this] show ?case using Weak_Early_Sim.monotonic by blast
qed

lemma weakBisimCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi
  and   X :: "(pi \<times> pi) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto><(X \<union> weakBisim)> S"
  and     "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<approx> Q"
using assms
by(coinduct rule: weakBisimCoinductAux) auto

lemma weakBisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi
  and   X :: "(pi \<times> pi) set"

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto><X> Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
using assms
by(coinduct rule: weakBisimWeakCoinductAux) auto

lemma weakBisimE:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx> Q"
  
  shows "P \<leadsto><weakBisim> Q"
  and   "Q \<approx> P"
using assms
by(auto dest: weakBisim.cases)

lemma weakBisimI:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<leadsto><weakBisim> Q"
  and     "Q \<approx> P"

  shows "P \<approx> Q"
using assms
by(auto intro: weakBisim.intros)

lemma eqvt[simp]:
  shows "eqvt weakBisim"
proof(auto simp add: eqvt_def)
  let ?X = "{x. \<exists>P Q (perm::name prm). P \<approx> Q \<and> x = (perm \<bullet> P, perm \<bullet> Q)}"
  fix P Q
  fix perm::"name prm"
  assume PBiSimQ: "P \<approx> Q"

  hence "(perm \<bullet> P, perm \<bullet> Q) \<in> ?X" by blast
  moreover have "\<And>P Q perm::name prm. \<lbrakk>P \<leadsto><weakBisim> Q\<rbrakk> \<Longrightarrow> (perm \<bullet> P) \<leadsto><?X> (perm \<bullet> Q)"
  proof -
    fix P Q
    fix perm::"name prm"
    assume "P \<leadsto><weakBisim> Q"

    moreover have "weakBisim \<subseteq> ?X"
    proof(auto)
      fix P Q
      assume "P \<approx> Q"
      moreover have "P = ([]::name prm) \<bullet> P" and "Q = ([]::name prm) \<bullet> Q" by auto
      ultimately show "\<exists>P' Q'. P' \<approx> Q' \<and> (\<exists>(perm::name prm). P = perm \<bullet> P' \<and> Q = perm \<bullet> Q')"
        by blast
    qed

    moreover have "eqvt ?X"
    proof(auto simp add: eqvt_def)
      fix P Q
      fix perm1::"name prm"
      fix perm2::"name prm"

      assume "P \<approx> Q"
      moreover have "perm1 \<bullet> perm2 \<bullet> P = (perm1 @ perm2) \<bullet> P" by(simp add: pt2[OF pt_name_inst])
      moreover have "perm1 \<bullet> perm2 \<bullet> Q = (perm1 @ perm2) \<bullet> Q" by(simp add: pt2[OF pt_name_inst])

      ultimately show "\<exists>P' Q'. P' \<approx> Q' \<and> (\<exists>(perm::name prm). perm1 \<bullet> perm2 \<bullet> P = perm \<bullet> P' \<and>
                                                              perm1 \<bullet> perm2 \<bullet> Q = perm \<bullet> Q')"
        by blast
    qed

    ultimately show "(perm \<bullet> P) \<leadsto><?X> (perm \<bullet> Q)"
      by(rule Weak_Early_Sim.eqvtI)
    qed

    ultimately show "(perm \<bullet> P) \<approx> (perm \<bullet> Q)" by(coinduct rule: weakBisimWeakCoinductAux, blast dest: weakBisimE)
qed

lemma eqvtI[eqvt]:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<approx> Q"

  shows "(perm \<bullet> P) \<approx> (perm \<bullet> Q)"
using assms
by(rule eqvtRelI[OF eqvt])

lemma strongBisimWeakBisim:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"

  shows "P \<approx> Q"
proof -
  from \<open>P \<sim> Q\<close> show ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cSim P Q)
    from \<open>P \<sim> Q\<close> have "P \<leadsto>[bisim] Q" by(rule bisimE)
    thus "P \<leadsto><bisim> Q" by(rule strongSimWeakSim)
  next
    case(cSym P Q)
    thus ?case by(rule bisimE)
  qed
qed

lemma reflexive:
  fixes P :: pi

  shows "P \<approx> P"
proof -
  have "(P, P) \<in> Id" by simp
  thus ?thesis
    by(coinduct rule: weakBisimCoinduct) (auto intro: Weak_Early_Sim.reflexive)
qed

lemma symetric:
  fixes P :: pi
  and   Q :: pi
   
  assumes "P \<approx> Q"

  shows "Q \<approx> P"
using assms
by(auto dest: weakBisimE)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<approx> Q"
  and     "Q \<approx> R"

  shows "P \<approx> R"
proof -
  let ?X = "weakBisim O weakBisim"
  from assms have "(P, R) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: weakBisimCoinduct)
    case(cSim P R)
    from \<open>(P, R) \<in> ?X\<close> obtain Q where "P \<approx> Q" and "Q \<approx> R" by auto
    from \<open>Q \<approx> R\<close> have "Q \<leadsto><weakBisim> R" by(rule weakBisimE)
    moreover have "eqvt ?X" by auto
    moreover have "?X \<subseteq> ?X" by simp
    ultimately show "P \<leadsto><(?X \<union> weakBisim)> R" using weakBisimE(1) \<open>P \<approx> Q\<close>
      by(rule_tac Weak_Early_Sim.transitive) auto
  next
    case(cSym P R)
    thus ?case by(auto dest: symetric)
  qed
qed

lemma weakBisimWeakUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto><(weakBisim O X O bisim)> Q"
  and rSym: "\<And> P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
proof -
  let ?X = "weakBisim O X O weakBisim"
  let ?Y = "weakBisim O X O bisim"
  from  Eqvt eqvt have "eqvt ?X" by blast
  from Strong_Early_Bisim.eqvt Eqvt eqvt have "eqvt ?Y" by blast

  from \<open>(P, Q) \<in> X\<close> have "(P, Q) \<in> ?X" by(blast intro: Strong_Early_Bisim.reflexive reflexive)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cSim P Q)
    {
      fix P P' Q' Q
      assume "P \<approx> P'" and "(P', Q') \<in> X" and "Q' \<approx> Q"
      from \<open>Q' \<approx> Q\<close> have "Q' \<leadsto><weakBisim> Q" by(rule weakBisimE)
      moreover note \<open>eqvt ?Y\<close> \<open>eqvt ?X\<close>
      moreover have "?Y O weakBisim \<subseteq> ?X" by(blast dest: strongBisimWeakBisim transitive)
      moreover {
        fix P Q
        assume "(P, Q) \<in> ?Y"
        then obtain P' Q' where "P \<approx> P'" and "(P', Q') \<in> X" and "Q' \<sim> Q" by auto
        from \<open>(P', Q') \<in> X\<close> have "P' \<leadsto><?Y> Q'" by(rule rSim)
        moreover from \<open>Q' \<sim> Q\<close> have "Q' \<leadsto>[bisim] Q" by(rule bisimE)
        moreover note \<open>eqvt ?Y\<close>
        moreover have "?Y O bisim \<subseteq> ?Y" by(auto dest: Strong_Early_Bisim.transitive)
        ultimately have "P' \<leadsto><?Y> Q" by(rule strongAppend)
        moreover note \<open>P \<approx> P'\<close>
        moreover have "weakBisim O ?Y \<subseteq> ?Y" by(blast dest: transitive)
        ultimately have "P \<leadsto><?Y> Q" using weakBisimE(1) eqvt \<open>eqvt ?Y\<close>
          by(rule_tac Weak_Early_Sim.transitive)
      }
      moreover from \<open>(P', Q') \<in> X\<close> have "(P', Q') \<in> ?Y" by(blast intro: reflexive Strong_Early_Bisim.reflexive)
      ultimately have "P' \<leadsto><?X> Q" by(rule Weak_Early_Sim.transitive)
      moreover note \<open>P \<approx> P'\<close>
      moreover have "weakBisim O ?X \<subseteq> ?X" by(blast dest: transitive)
      ultimately have "P \<leadsto><?X> Q" using weakBisimE(1) eqvt \<open>eqvt ?X\<close>
        by(rule_tac Weak_Early_Sim.transitive)
    }
    with \<open>(P, Q) \<in> ?X\<close> show ?case by auto
  next
    case(cSym P Q)
    thus ?case 
      apply auto
      by(blast dest: bisimE rSym weakBisimE)
  qed
qed

lemma weakBisimUpto[case_names cSim cSym, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rSim: "\<And>R S. (R, S) \<in> X \<Longrightarrow> R \<leadsto><(weakBisim O (X \<union> weakBisim) O bisim)> S"
  and rSym: "\<And>R S. (R, S) \<in> X \<Longrightarrow> (S, R) \<in> X"

  shows "P \<approx> Q"
proof -
  from p  have "(P, Q) \<in> X \<union> weakBisim" by simp
  thus ?thesis using Eqvt
    apply(coinduct rule: weakBisimWeakUpto)
    apply(auto dest: rSim rSym weakBisimE)
    apply(rule Weak_Early_Sim.monotonic)
    apply(blast dest: weakBisimE)
    apply(auto simp add: relcomp_unfold)
    by(metis reflexive Strong_Early_Bisim.reflexive transitive)
qed


lemma transitive_coinduct_weak[case_names cSim cSym, consumes 2]:
  assumes p: "(P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto><(bisim O X O bisim)> Q"
  and rSym: "\<And> P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> bisim O X O bisim"

  shows "P \<approx> Q"
proof -
  let ?X = "bisim O X O bisim"
  from \<open>(P, Q) \<in> X\<close> have "(P, Q) \<in> ?X" by(blast intro: Strong_Early_Bisim.reflexive)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakCoinduct)
    case(cSim P Q)
    {
      fix P P' Q' Q
      assume PBisimP': "P \<sim> P'"
      assume P'SimQ': "P' \<leadsto><?X> Q'"
      assume Q'SimQ: "Q' \<leadsto>[bisim] Q"
      
      have "P \<leadsto><?X> Q"
      proof -
        have "P' \<leadsto><?X> Q"
        proof -
          have "?X O bisim \<subseteq> ?X" by(blast intro: Strong_Early_Bisim.transitive)
          moreover from Strong_Early_Bisim.eqvt Eqvt have "eqvt ?X" by blast
          ultimately show ?thesis using P'SimQ' Q'SimQ 
            by(rule_tac strongAppend)
        qed
        moreover have "eqvt bisim" by(rule Strong_Early_Bisim.eqvt)
        moreover from Strong_Early_Bisim.eqvt Eqvt have "eqvt ?X" by blast
        moreover have "bisim O ?X \<subseteq> ?X" by(blast intro: Strong_Early_Bisim.transitive)
        moreover have "\<And>P Q. P \<sim> Q \<Longrightarrow> P \<leadsto><bisim> Q" by(blast dest: Strong_Early_Bisim.bisimE strongSimWeakSim)
        ultimately show ?thesis using PBisimP' by(rule Weak_Early_Sim.transitive)
      qed
    }
    thus ?case using \<open>(P, Q) \<in> ?X\<close> rSim by (blast dest: Strong_Early_Bisim.bisimE)
  next
    case(cSym P Q)
    {
      fix P P' Q' Q
      assume "P \<sim> P'" and "(P', Q') \<in> X" and "Q' \<sim> Q"
      from \<open>(P', Q') \<in> X\<close> have "(Q', P') \<in> ?X" by(rule rSym)
      with \<open>P \<sim> P'\<close> \<open>Q' \<sim> Q\<close> have "(Q, P) \<in> ?X" 
        apply auto
        apply(drule_tac Strong_Early_Bisim.bisimE(2))
        apply(drule Strong_Early_Bisim.transitive[where Q=P'])
        apply assumption
        apply(drule_tac Strong_Early_Bisim.bisimE(2))
        apply(drule Strong_Early_Bisim.transitive[where Q=Q'])
        apply assumption
        by auto
    }
    thus ?case using \<open>(P, Q) \<in> ?X\<close> by auto
  qed
qed

end
