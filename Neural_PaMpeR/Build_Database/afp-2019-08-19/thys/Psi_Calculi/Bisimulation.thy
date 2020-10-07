(* 
   Title: Psi-calculi   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Bisimulation
  imports Simulation
begin

context env begin

lemma monoCoinduct: "\<And>x y xa xb xc P Q \<Psi>.
                      x \<le> y \<Longrightarrow>
                      (\<Psi> \<rhd> Q \<leadsto>[{(xc, xb, xa). x xc xb xa}] P) \<longrightarrow>
                     (\<Psi> \<rhd> Q \<leadsto>[{(xb, xa, xc). y xb xa xc}] P)"
apply auto
apply(rule monotonic)
by(auto dest: le_funE)

coinductive_set bisim :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set" 
where
  step: "\<lbrakk>(insertAssertion (extractFrame P)) \<Psi> \<simeq>\<^sub>F (insertAssertion (extractFrame Q) \<Psi>);
          \<Psi> \<rhd> P \<leadsto>[bisim] Q;
          \<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>',  P, Q) \<in> bisim; (\<Psi>, Q, P) \<in> bisim\<rbrakk> \<Longrightarrow> (\<Psi>, P, Q) \<in> bisim"
monos monoCoinduct

abbreviation
  bisimJudge ("_ \<rhd> _ \<sim> _" [70, 70, 70] 65) where "\<Psi> \<rhd> P \<sim> Q \<equiv> (\<Psi>, P, Q) \<in> bisim"
abbreviation
  bisimNilJudge ("_ \<sim> _" [70, 70] 65) where "P \<sim> Q \<equiv> SBottom' \<rhd> P \<sim> Q"

lemma bisimCoinductAux[consumes 1]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi> \<and>
                                    (\<Psi> \<rhd> P \<leadsto>[(X \<union> bisim)] Q) \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim) \<and>
                                    ((\<Psi>, Q, P) \<in> X \<or> (\<Psi>, Q, P) \<in> bisim)"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisimCoinduct[consumes 1, case_names cStatEq cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> insertAssertion (extractFrame R) \<Psi>' \<simeq>\<^sub>F insertAssertion (extractFrame S) \<Psi>'"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[(X \<union> bisim)] S"
  and     "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> bisim"
  and     "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> (\<Psi>', S, R) \<in> bisim"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
    by coinduct simp
qed

lemma bisimWeakCoinductAux[consumes 1]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi> \<and>
                                     \<Psi> \<rhd> P \<leadsto>[X] Q \<and>
                                    (\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X) \<and> (\<Psi>, Q, P) \<in> X" 

  shows "(\<Psi>, P, Q) \<in> bisim"
using assms
by(coinduct rule: bisimCoinductAux) (blast intro: monotonic)

lemma bisimWeakCoinduct[consumes 1, case_names cStatEq cSim cExt cSym]:
  fixes F :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes "(\<Psi>, P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[X] Q"
  and     "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and     "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "(\<Psi>, P, Q) \<in> bisim"
proof -
  have "X \<union> bisim = {(\<Psi>, P, Q). (\<Psi>, P, Q) \<in> X \<or> (\<Psi>, P, Q) \<in> bisim}" by auto
  with assms show ?thesis
  by(coinduct rule: bisimCoinduct) (blast intro: monotonic)+
qed

lemma bisimE:
  fixes P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>  :: 'b
  and   \<Psi>' :: 'b

  assumes "(\<Psi>, P, Q) \<in> bisim"

  shows "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and   "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
  and   "(\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
  and   "(\<Psi>, Q, P) \<in> bisim"
using assms
by(auto simp add: intro: bisim.cases)

lemma bisimI:
  fixes P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   \<Psi> :: 'b

  assumes "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and     "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
  and     "\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
  and     "(\<Psi>, Q, P) \<in> bisim"

  shows "(\<Psi>, P, Q) \<in> bisim"
using assms
by(auto intro: bisim.step)

lemma bisimReflexive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"


  shows "\<Psi> \<rhd> P \<sim> P"
proof -
  let ?X = "{(\<Psi>, P, P) | \<Psi> P. True}"
  have "(\<Psi>, P, P) \<in> ?X" by simp
  thus ?thesis
    by(coinduct rule: bisimWeakCoinduct, auto intro: reflexive)
qed

lemma bisimClosed:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   p :: "name prm"
  
  assumes PBisimQ: "\<Psi> \<rhd> P \<sim> Q"

  shows "(p \<bullet> \<Psi>) \<rhd>  (p \<bullet> P) \<sim> (p \<bullet> Q)"
proof -
  let ?X = "{(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) | (p::name prm) \<Psi>  P Q. \<Psi> \<rhd> P \<sim> Q}"
  from PBisimQ have "(p \<bullet> \<Psi>, p \<bullet> P, p \<bullet> Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> P Q)
    have "\<And>\<Psi> P Q (p::name prm). insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi> \<Longrightarrow>
          insertAssertion (extractFrame(p \<bullet> P)) (p \<bullet> \<Psi>) \<simeq>\<^sub>F insertAssertion (extractFrame(p \<bullet> Q))  (p \<bullet> \<Psi>)"
      by(drule_tac p = p in FrameStatEqClosed) (simp add: eqvts)
      
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case by(blast dest: bisimE)
  next
    case(cSim \<Psi> P Q)
    {
      fix p :: "name prm"
      fix \<Psi> P Q
      have "eqvt ?X"
        apply(auto simp add: eqvt_def)
        apply(rule_tac x="pa@p" in exI)
        by(auto simp add: pt2[OF pt_name_inst])
      moreover assume "\<Psi> \<rhd> P \<leadsto>[bisim] Q"
      hence "\<Psi> \<rhd> P \<leadsto>[?X] Q"
        apply(rule_tac A=bisim in monotonic, auto)
        by(rule_tac x="[]::name prm" in exI) auto
      ultimately have "((p::name prm) \<bullet> \<Psi>) \<rhd> (p \<bullet> P) \<leadsto>[?X] (p \<bullet> Q)"
        by(rule_tac simClosed)
    }
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cExt \<Psi> P Q \<Psi>')
    {
      fix p :: "name prm"
      fix \<Psi> P Q \<Psi>'
      assume "\<forall>\<Psi>'. (\<Psi> \<otimes> \<Psi>', P, Q) \<in> bisim"
      hence "((p \<bullet> \<Psi>) \<otimes> \<Psi>', p \<bullet> P, p \<bullet> Q) \<in> ?X"  
        apply(auto, rule_tac x=p in exI)
        apply(rule_tac x="\<Psi> \<otimes> (rev p \<bullet> \<Psi>')" in exI)
        by(auto simp add: eqvts)
    }
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cSym \<Psi> P Q)
    thus ?case
      by(blast dest: bisimE)
  qed
qed

lemma bisimEqvt[simp]:
  shows "eqvt bisim"
by(auto simp add: eqvt_def bisimClosed)

lemma statEqBisim:
  fixes \<Psi>  :: 'b
  and   P  :: "('a, 'b, 'c) psi"
  and   Q  :: "('a, 'b, 'c) psi"
  and   \<Psi>' :: 'b
  
  assumes "\<Psi> \<rhd> P \<sim> Q"
  and     "\<Psi> \<simeq> \<Psi>'"

  shows "\<Psi>' \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>', P, Q) | \<Psi> P Q \<Psi>'. \<Psi> \<rhd> P \<sim> Q \<and> \<Psi> \<simeq> \<Psi>'}"
  from \<open>\<Psi> \<rhd> P \<sim> Q\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close> have "(\<Psi>', P, Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi>' P Q)
    from \<open>(\<Psi>', P, Q) \<in> ?X\<close> obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have PeqQ: "insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
      by(rule bisimE)

    obtain A\<^sub>P \<Psi>\<^sub>P where FrP: "extractFrame P = \<langle>A\<^sub>P, \<Psi>\<^sub>P\<rangle>" and "A\<^sub>P \<sharp>* \<Psi>" and "A\<^sub>P \<sharp>* \<Psi>'"
      by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto
    obtain A\<^sub>Q \<Psi>\<^sub>Q where FrQ: "extractFrame Q = \<langle>A\<^sub>Q, \<Psi>\<^sub>Q\<rangle>" and "A\<^sub>Q \<sharp>* \<Psi>" and "A\<^sub>Q \<sharp>* \<Psi>'"
      by(rule_tac C="(\<Psi>, \<Psi>')" in freshFrame) auto

    from PeqQ FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>\<close> \<open>\<Psi> \<simeq> \<Psi>'\<close>
    have "\<langle>A\<^sub>P, \<Psi>' \<otimes> \<Psi>\<^sub>P\<rangle> \<simeq>\<^sub>F \<langle>A\<^sub>Q, \<Psi>' \<otimes> \<Psi>\<^sub>Q\<rangle>"
      by simp (metis frameIntComposition FrameStatEqTrans FrameStatEqSym)
    with FrP FrQ \<open>A\<^sub>P \<sharp>* \<Psi>'\<close> \<open>A\<^sub>Q \<sharp>* \<Psi>'\<close> show ?case by simp
  next
    case(cSim \<Psi>' P Q)
    from \<open>(\<Psi>', P, Q) \<in> ?X\<close> obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> P \<leadsto>[bisim] Q" by(blast dest: bisimE)
    moreover have "eqvt ?X"
      by(auto simp add: eqvt_def) (metis bisimClosed AssertionStatEqClosed)
    hence "eqvt(?X \<union> bisim)" by auto
    moreover note \<open>\<Psi> \<simeq> \<Psi>'\<close>
    moreover have "\<And>\<Psi> P Q \<Psi>'. \<lbrakk>\<Psi> \<rhd> P \<sim> Q; \<Psi> \<simeq> \<Psi>'\<rbrakk> \<Longrightarrow> (\<Psi>', P, Q) \<in> ?X \<union> bisim"
      by auto
    ultimately show ?case
      by(rule statEqSim)
  next
    case(cExt \<Psi>' P Q \<Psi>'')
    from \<open>(\<Psi>', P, Q) \<in> ?X\<close> obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<otimes> \<Psi>'' \<rhd> P \<sim> Q" by(rule bisimE)
    moreover from \<open>\<Psi> \<simeq> \<Psi>'\<close> have "\<Psi> \<otimes> \<Psi>'' \<simeq> \<Psi>' \<otimes> \<Psi>''" by(rule Composition)
    ultimately show ?case by blast
  next
    case(cSym \<Psi>' P Q)
    from \<open>(\<Psi>', P, Q) \<in> ?X\<close> obtain \<Psi> where "\<Psi> \<rhd> P \<sim> Q" and "\<Psi> \<simeq> \<Psi>'"
      by auto
    from \<open>\<Psi> \<rhd> P \<sim> Q\<close> have "\<Psi> \<rhd> Q \<sim> P" by(rule bisimE)
    thus ?case using \<open>\<Psi> \<simeq> \<Psi>'\<close> by auto
  qed
qed

lemma bisimTransitive:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   R :: "('a, 'b, 'c) psi"

  assumes PQ: "\<Psi> \<rhd> P \<sim> Q"
  and     QR: "\<Psi> \<rhd> Q \<sim> R"

  shows "\<Psi> \<rhd> P \<sim> R"
proof -
  let ?X = "{(\<Psi>, P, R) | \<Psi> P Q R. \<Psi> \<rhd> P \<sim> Q \<and> \<Psi> \<rhd> Q \<sim> R}" 
  from PQ QR have "(\<Psi>, P, R) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cStatEq \<Psi> P R)
    thus ?case by(blast dest: bisimE FrameStatEqTrans)
  next
    case(cSim \<Psi> P R)
    {
      fix \<Psi> P Q R
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] Q" and "\<Psi> \<rhd> Q \<leadsto>[bisim] R"
      moreover have "eqvt ?X"
        by(force simp add: eqvt_def dest: bisimClosed)
      with bisimEqvt have "eqvt (?X \<union> bisim)" by blast
      moreover have "?X \<subseteq> ?X \<union> bisim" by auto
      ultimately have "\<Psi> \<rhd> P \<leadsto>[(?X \<union> bisim)] R"
        by(force intro: transitive)
    }
    with \<open>(\<Psi>, P, R) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cExt \<Psi> P R \<Psi>')
    thus ?case by(blast dest: bisimE)
  next
    case(cSym \<Psi> P R)
    thus ?case by(blast dest: bisimE)
  qed
qed

lemma weakTransitiveCoinduct[case_names cStatEq cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatEq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi>, Q, P) \<in> X"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisimReflexive)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case
      by(blast dest: rStatEq bisimE FrameStatEqTrans)
  next
    case(cSim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'RelQ': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule rSim)
      moreover from \<open>eqvt X\<close> P'RelQ' have "eqvt ?X"
        apply(auto simp add: eqvt_def)
        apply(drule_tac p=p in bisimClosed)
        apply(drule_tac p=p in bisimClosed)
        apply(rule_tac x="p \<bullet> P'a" in exI, simp)
        by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
        by(force intro: transitive dest: bisimTransitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using \<open>eqvt ?X\<close>
        by(force intro: transitive dest: bisimTransitive)
    }
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE intro: rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: bisimE intro: rSym)
  qed
qed

lemma weakTransitiveCoinduct'[case_names cStatEq cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatEq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow>
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisimReflexive)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case
      by(blast dest: rStatEq bisimE FrameStatEqTrans)
  next
    case(cSim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'RelQ': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule rSim)
      moreover from \<open>eqvt X\<close> P'RelQ' have "eqvt ?X"
        apply(auto simp add: eqvt_def)
        apply(drule_tac p=p in bisimClosed)
        apply(drule_tac p=p in bisimClosed)
        apply(rule_tac x="p \<bullet> P'a" in exI, simp)
        by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
        by(force intro: transitive dest: bisimTransitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using \<open>eqvt ?X\<close>
        by(force intro: transitive dest: bisimTransitive)
    }
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(blast dest: bisimE intro: rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case
      apply auto
      apply(drule rSym)
      apply auto
      by(metis bisimTransitive bisimE(4))
  qed
qed

lemma weakTransitiveCoinduct''[case_names cStatEq cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatEq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> X \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q} \<Longrightarrow> 
                         (\<Psi> \<otimes> \<Psi>', P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q} \<Longrightarrow> 
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  let ?X = "{(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
  from p have "(\<Psi>, P, Q) \<in> ?X"
    by(blast intro: bisimReflexive)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cStatEq \<Psi> P Q)
    thus ?case
      by(blast dest: rStatEq bisimE FrameStatEqTrans)
  next
    case(cSim \<Psi> P Q)
    {
      fix \<Psi> P P' Q' Q
      assume "\<Psi> \<rhd> P \<leadsto>[bisim] P'"
      moreover assume P'RelQ': "(\<Psi>, P', Q') \<in> X"
      hence "\<Psi> \<rhd> P' \<leadsto>[?X] Q'" by(rule rSim)
      moreover from \<open>eqvt X\<close> P'RelQ' have "eqvt ?X"
        apply(auto simp add: eqvt_def)
        apply(drule_tac p=p in bisimClosed)
        apply(drule_tac p=p in bisimClosed)
        apply(rule_tac x="p \<bullet> P'a" in exI, simp)
        by(rule_tac x="p \<bullet> Q'a" in exI, auto)
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q'"
        by(force intro: transitive dest: bisimTransitive)
      moreover assume "\<Psi> \<rhd> Q' \<leadsto>[bisim] Q"
      ultimately have "\<Psi> \<rhd> P \<leadsto>[?X] Q" using \<open>eqvt ?X\<close>
        by(force intro: transitive dest: bisimTransitive)
    }
    with \<open>(\<Psi>, P, Q) \<in> ?X\<close> show ?case
      by(blast dest: bisimE)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case by(rule_tac rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(rule_tac rSym)
  qed
qed

lemma transitiveCoinduct[case_names cStatEq cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatEq: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> insertAssertion (extractFrame R) \<Psi>' \<simeq>\<^sub>F insertAssertion (extractFrame S) \<Psi>'"
  and rSim: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> \<Psi>' \<rhd> R \<leadsto>[({(\<Psi>', R, S) | \<Psi>' R R' S' S. \<Psi>' \<rhd> R \<sim> R' \<and>
                                                                        ((\<Psi>', R', S') \<in> X \<or> \<Psi>' \<rhd> R' \<sim> S') \<and>
                                                                        \<Psi>' \<rhd> S' \<sim> S})] S"
  and rExt: "\<And>\<Psi>' R S \<Psi>''. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>' \<otimes> \<Psi>'', R, S) \<in> X \<or> \<Psi>' \<otimes> \<Psi>'' \<rhd> R \<sim> S"
  and rSym: "\<And>\<Psi>' R S. (\<Psi>', R, S) \<in> X \<Longrightarrow> (\<Psi>', S, R) \<in> X \<or> \<Psi>' \<rhd> S \<sim> R"


  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> (X \<union> bisim)"
    by blast
  moreover from \<open>eqvt X\<close> bisimEqvt have "eqvt (X \<union> bisim)"
    by auto
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct')
    case(cStatEq \<Psi> P Q)
    thus ?case
      by(blast intro: rStatEq dest: bisimE)
  next
    case(cSim \<Psi> P Q)
    thus ?case
      apply auto
      apply(blast intro: rSim)
      apply(drule bisimE(2))
      apply(rule_tac A=bisim in monotonic, simp)
      by(force intro: bisimReflexive)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case
      by(blast dest: bisimE rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case by(blast dest: bisimE rSym intro: bisimReflexive)
  qed
qed

lemma transitiveCoinduct'[case_names cStatEq cSim cExt cSym, case_conclusion bisim step, consumes 2]:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"
  and   X :: "('b \<times> ('a, 'b, 'c) psi \<times> ('a, 'b, 'c) psi) set"

  assumes p: "(\<Psi>, P, Q) \<in> X"
  and Eqvt: "eqvt X"
  and rStatEq: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> insertAssertion (extractFrame P) \<Psi> \<simeq>\<^sub>F insertAssertion (extractFrame Q) \<Psi>"
  and rSim: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow> \<Psi> \<rhd> P \<leadsto>[({(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and>
                                                                        (\<Psi>, P', Q') \<in> (X \<union> bisim) \<and>
                                                                        \<Psi> \<rhd> Q' \<sim> Q})] Q"
  and rExt: "\<And>\<Psi> P Q \<Psi>'. (\<Psi>, P, Q) \<in> X \<Longrightarrow> (\<Psi> \<otimes> \<Psi>', P, Q) \<in> X \<or> \<Psi> \<otimes> \<Psi>' \<rhd> P \<sim> Q"
  and rSym: "\<And>\<Psi> P Q. (\<Psi>, P, Q) \<in> X \<Longrightarrow>
                      (\<Psi>, Q, P) \<in> {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> (X \<union> bisim)) \<and> \<Psi> \<rhd> Q' \<sim> Q}"

  shows "\<Psi> \<rhd> P \<sim> Q"
proof -
  from p have "(\<Psi>, P, Q) \<in> (X \<union> bisim)"
    by blast
  moreover from \<open>eqvt X\<close> bisimEqvt have "eqvt (X \<union> bisim)"
    by auto
  ultimately show ?thesis
  proof(coinduct rule: weakTransitiveCoinduct')
    case(cStatEq \<Psi> P Q)
    thus ?case
      by(blast intro: rStatEq dest: bisimE)
  next
    case(cSim \<Psi> P Q)
    thus ?case
      apply -
      apply(case_tac "(\<Psi>, P, Q) \<in> X" for X)
      apply(rule_tac rSim)
      apply simp
      apply(clarify)
      apply(drule bisimE(2))
      apply(rule_tac A=bisim in monotonic, simp)
      by(force intro: bisimReflexive)
  next
    case(cExt \<Psi> P Q \<Psi>')
    thus ?case
      by(blast dest: bisimE rExt)
  next
    case(cSym \<Psi> P Q)
    thus ?case
      apply auto
      apply(drule rSym)
      apply auto
      apply(rule_tac x=Q in exI)
      apply(auto intro: bisimReflexive)
      apply(rule_tac x=P in exI)
      by(auto intro: bisimReflexive dest: bisimE(4))
  qed
qed

lemma bisimSymmetric:
  fixes \<Psi> :: 'b
  and   P :: "('a, 'b, 'c) psi"
  and   Q :: "('a, 'b, 'c) psi"

  assumes "\<Psi> \<rhd> P \<sim> Q"
  
  shows "\<Psi> \<rhd> Q \<sim> P"
using assms
by(rule bisimE)

lemma eqvtTrans[intro]:
  assumes "eqvt X"

  shows "eqvt {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> ((\<Psi>, P', Q') \<in> X \<or> \<Psi> \<rhd> P' \<sim> Q') \<and> \<Psi> \<rhd> Q' \<sim> Q}"
using assms
apply(auto simp add: eqvt_def eqvts)
apply(erule_tac x="(a, P', Q')" in ballE, auto)
by(blast dest: bisimClosed)+

lemma eqvtWeakTrans[intro]:
  assumes "eqvt X"

  shows "eqvt {(\<Psi>, P, Q) | \<Psi> P P' Q' Q. \<Psi> \<rhd> P \<sim> P' \<and> (\<Psi>, P', Q') \<in> X \<and> \<Psi> \<rhd> Q' \<sim> Q}"
using assms
apply(auto simp add: eqvt_def eqvts)
apply(erule_tac x="(a, P', Q')" in ballE, auto)
by(blast dest: bisimClosed)+

end

end


