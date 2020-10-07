(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Bisim
  imports Weak_Late_Sim Strong_Late_Bisim
begin

lemma monoAux: "A \<subseteq> B \<Longrightarrow> P \<leadsto>\<^sup>^<A> Q \<longrightarrow> P \<leadsto>\<^sup>^<B> Q"
by(auto intro: Weak_Late_Sim.monotonic)

coinductive_set weakBisim :: "(pi \<times> pi) set"
where
  step: "\<lbrakk>P \<leadsto>\<^sup>^<weakBisim> Q; (Q, P) \<in> weakBisim\<rbrakk> \<Longrightarrow> (P, Q) \<in> weakBisim"
monos monoAux

abbreviation
  "weakBisimJudge" (infixr "\<approx>" 65)  where "P \<approx> Q \<equiv> (P, Q) \<in> weakBisim"

lemma weakBisimCoinductAux[case_names weakBisim, case_conclusion weakBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(X \<union> weakBisim)> Q \<and> ((Q, P) \<in> X \<or> Q \<approx> P)"

  shows "P \<approx> Q"
proof -
  have aux: "X \<union> weakBisim = {(P, Q). (P, Q) \<in> X \<or> P \<approx> Q}" by blast

  from p show ?thesis
    by(coinduct, force dest: step simp add: aux)
qed

lemma weakBisimCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(X \<union> weakBisim)> Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
using assms
by(coinduct rule: weakBisimCoinductAux) auto

lemma weak_coinduct[case_names weakBisim, case_conclusion weakBisim step, consumes 1]:
  assumes p: "(P, Q) \<in> X"
  and step:  "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<X> Q \<and> (Q, P) \<in> X"

  shows "P \<approx> Q"
using p
proof(coinduct rule: weakBisimCoinductAux)
  case (weakBisim P Q)
  from step[OF this] show ?case using Weak_Late_Sim.monotonic by blast
qed

lemma weakBisimWeakCoinduct[consumes 1, case_names cSim cSym]:
  fixes P :: pi
  and   Q :: pi

  assumes "(P, Q) \<in> X"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<X> Q"
  and     "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
using assms
by(coinduct rule: weak_coinduct) auto
lemma monotonic: "mono(\<lambda>p x1 x2. \<exists>P Q. x1 = P \<and> x2 = Q \<and> P \<leadsto>\<^sup>^<{(xa, x). p xa x}> Q \<and> Q \<leadsto>\<^sup>^<{(xa, x). p xa x}> P)"
by(auto intro: monoI Weak_Late_Sim.monotonic)

lemma unfoldE:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<approx> Q"
  
  shows "P \<leadsto>\<^sup>^<weakBisim> Q"
  and   "Q \<approx> P"
using assms
by(auto intro: weakBisim.cases)

lemma unfoldI:
  fixes P :: pi
  and   Q :: pi
  
  assumes "P \<leadsto>\<^sup>^<weakBisim> Q"
  and     "Q \<approx> P"

  shows "P \<approx> Q"
using assms
by(auto intro: weakBisim.cases)

lemma eqvt:
  shows "eqvt weakBisim"
proof(auto simp add: eqvt_def)
  let ?X = "{x. \<exists>P Q (perm::name prm). P \<approx> Q \<and> x = (perm \<bullet> P, perm \<bullet> Q)}"
  fix P Q
  fix perm::"name prm"
  assume PBiSimQ: "P \<approx> Q"

  hence "(perm \<bullet> P, perm \<bullet> Q) \<in> ?X" by blast
  moreover have "\<And>P Q perm::name prm. \<lbrakk>P \<leadsto>\<^sup>^<weakBisim> Q\<rbrakk> \<Longrightarrow> (perm \<bullet> P) \<leadsto>\<^sup>^<?X> (perm \<bullet> Q)"
  proof -
    fix P Q
    fix perm::"name prm"
    assume "P \<leadsto>\<^sup>^<weakBisim> Q"

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

    ultimately show "(perm \<bullet> P) \<leadsto>\<^sup>^<?X> (perm \<bullet> Q)"
      by(rule Weak_Late_Sim.eqvtI)
    qed

    ultimately show "(perm \<bullet> P) \<approx> (perm \<bullet> Q)" by(coinduct rule: weak_coinduct, blast dest: unfoldE)
qed

lemma eqvtI:
  fixes P :: pi
  and   Q :: pi
  and   perm :: "name prm"

  assumes "P \<approx> Q"

  shows "(perm \<bullet> P) \<approx> (perm \<bullet> Q)"
using assms
by(rule eqvtRelI[OF eqvt])

lemma weakBisimEqvt[simp]:
  shows "eqvt weakBisim"
by(auto simp add: eqvt_def eqvtI)

lemma strongBisimWeakBisim:
  fixes P :: pi
  and   Q :: pi

  assumes PSimQ: "P \<sim> Q"

  shows "P \<approx> Q"
proof -
  have "\<And>P Q. P \<leadsto>[bisim] Q \<Longrightarrow> P \<leadsto>\<^sup>^<(bisim \<union> weakBisim)> Q"
  proof -
    fix P Q
    assume "P \<leadsto>[bisim] Q"
    hence "P \<leadsto>\<^sup>^<bisim> Q" by(rule strongSimWeakSim)
    thus "P \<leadsto>\<^sup>^<(bisim \<union> weakBisim)> Q"
      by(blast intro: Weak_Late_Sim.monotonic)
  qed

  with PSimQ show ?thesis
    by(coinduct rule: weakBisimCoinductAux, force dest: Strong_Late_Bisim.bisimE symmetric)
qed

lemma reflexive:
  fixes P :: pi

  shows "P \<approx> P"
proof -
  have "(P, P) \<in> Id" by simp
  then show ?thesis

  proof (coinduct rule: weak_coinduct)
    case (weakBisim P Q)
    have "(P, Q) \<in> Id" by fact
    thus ?case by(auto intro: Weak_Late_Sim.reflexive)
  qed
qed

lemma symmetric:
  fixes P :: pi
  and   Q :: pi
   
  assumes "P \<approx> Q"

  shows "Q \<approx> P"
using assms
by(auto dest: unfoldE intro: unfoldI)

lemma transitive:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes PBiSimQ: "P \<approx> Q"
  and     QBiSimR: "Q \<approx> R"

  shows "P \<approx> R"
proof -
  let ?X = "weakBisim O weakBisim"
  from assms have "(P, R) \<in> ?X" by blast
  moreover have "\<And>P Q R. \<lbrakk>Q \<leadsto>\<^sup>^<weakBisim> R; P \<approx> Q\<rbrakk> \<Longrightarrow>
                          P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> R"
  proof -
    fix P Q R
    assume PBiSimQ: "P \<approx> Q"
    assume "Q \<leadsto>\<^sup>^<weakBisim> R"
    moreover have "eqvt weakBisim" by(rule eqvt)
    moreover from eqvt have "eqvt (?X \<union> weakBisim)" by(auto simp add: eqvtTrans)
    moreover have "weakBisim O weakBisim \<subseteq> ?X \<union> weakBisim" by auto
    moreover have "\<And>P Q. P \<approx> Q \<Longrightarrow> P \<leadsto>\<^sup>^<weakBisim> Q" by(rule unfoldE)

    ultimately show "P \<leadsto>\<^sup>^<(?X \<union> weakBisim)> R" using PBiSimQ
      by(rule Weak_Late_Sim.transitive)
  qed

  ultimately show ?thesis
    apply(coinduct rule: weakBisimCoinduct, auto)
    by(blast dest: unfoldE symmetric)+
qed


lemma transitive_coinduct_weak[case_names WeakBisimEarly, case_conclusion WeakBisimEarly step, consumes 2]:
  assumes p: "(P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and step: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(bisim O X O bisim)> Q \<and> (Q, P) \<in> X"

  shows "P \<approx> Q"
proof -
  let ?X = "bisim O X O bisim"

  have Sim: "\<And>P P' Q' Q. \<lbrakk>P \<sim> P'; P'\<leadsto>\<^sup>^<?X> Q'; Q' \<leadsto>[bisim] Q\<rbrakk> \<Longrightarrow>
                          P \<leadsto>\<^sup>^<?X> Q"
  proof -
    fix P P' Q' Q
    assume PBisimP': "P \<sim> P'"
    assume P'SimQ': "P' \<leadsto>\<^sup>^<?X> Q'"
    assume Q'SimQ: "Q' \<leadsto>[bisim] Q"

    show "P \<leadsto>\<^sup>^<?X> Q"
    proof -
      have "P' \<leadsto>\<^sup>^<?X> Q"
      proof -
        have "?X O bisim \<subseteq> ?X" by(blast intro: Strong_Late_Bisim.transitive)
        moreover from Strong_Late_Bisim.bisimEqvt Eqvt have "eqvt ?X" by blast
        ultimately show ?thesis using P'SimQ' Q'SimQ by(blast intro: strongAppend)
      qed
      moreover have "eqvt bisim" by(rule Strong_Late_Bisim.bisimEqvt)
      moreover from Strong_Late_Bisim.bisimEqvt Eqvt have "eqvt ?X" by blast
      moreover have "bisim O ?X \<subseteq> ?X" by(blast intro: Strong_Late_Bisim.transitive)
      moreover have "\<And>P Q. P \<sim> Q \<Longrightarrow> P \<leadsto>\<^sup>^<bisim> Q" by(blast dest: Strong_Late_Bisim.bisimE strongSimWeakSim)
      ultimately show ?thesis using PBisimP' by(rule Weak_Late_Sim.transitive)
    qed
  qed

  from p have "(P, Q) \<in> ?X" by(blast intro: Strong_Late_Bisim.reflexive)
  moreover from step Sim have "\<And>P Q. (P, Q) \<in> ?X \<Longrightarrow> P \<leadsto>\<^sup>^<?X> Q \<and> (Q, P) \<in> ?X"
    by(blast dest: Strong_Late_Bisim.bisimE Strong_Late_Bisim.symmetric)

  ultimately show ?thesis by(rule weak_coinduct)
qed

lemma weakBisimTransitiveCoinduct[case_names cSim cSym, consumes 2]:
  assumes p: "(P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rSim: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> P \<leadsto>\<^sup>^<(bisim O X O bisim)> Q"
  and rSym: "\<And>P Q. (P, Q) \<in> X \<Longrightarrow> (Q, P) \<in> X"

  shows "P \<approx> Q"
using assms
by(coinduct rule: transitive_coinduct_weak) auto

end
