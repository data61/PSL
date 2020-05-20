(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Bisim_Pres
  imports Strong_Late_Bisim Strong_Late_Sim_Pres
begin

lemma tauPres:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"

  shows "\<tau>.(P) \<sim> \<tau>.(Q)"
proof -
  let ?X = "{(\<tau>.(P), \<tau>.(Q)), (\<tau>.(Q), \<tau>.(P))}"
  have "(\<tau>.(P), \<tau>.(Q)) \<in> ?X" by auto
  thus ?thesis using \<open>P \<sim> Q\<close>
    by(coinduct rule: bisimCoinduct)
      (auto intro: Strong_Late_Sim_Pres.tauPres dest: symmetric)
qed

lemma inputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   x :: name

  assumes PSimQ: "\<forall>y. P[x::=y] \<sim> Q[x::=y]"
  
  shows "a<x>.P \<sim> a<x>.Q"
proof -
  let ?X = "{(a<x>.P, a<x>.Q) | a x P Q. \<forall>y. P[x::=y] \<sim> Q[x::=y]}"
  {
    fix axP axQ p
    assume "(axP, axQ) \<in> ?X"
    then obtain a x P Q where A: "\<forall>y. P[x::=y] \<sim> Q[x::=y]" and B: "axP = a<x>.P" and C: "axQ = a<x>.Q"
      by auto
    have "\<And>y. ((p::name prm) \<bullet> P)[(p \<bullet> x)::=y] \<sim> (p \<bullet> Q)[(p \<bullet> x)::=y]"
    proof -
      fix y
      from A have "P[x::=(rev p \<bullet> y)] \<sim> Q[x::=(rev p \<bullet> y)]"
        by blast
      hence "(p \<bullet> (P[x::=(rev p \<bullet> y)])) \<sim> p \<bullet> (Q[x::=(rev p \<bullet> y)])"
        by(rule bisimClosed)
      thus "(p \<bullet> P)[(p \<bullet> x)::=y] \<sim> (p \<bullet> Q)[(p \<bullet> x)::=y]"
        by(simp add: eqvts pt_pi_rev[OF pt_name_inst, OF at_name_inst])
    qed
    hence "((p::name prm) \<bullet> axP, p \<bullet> axQ) \<in> ?X" using B C
      by auto
  }
  hence "eqvt ?X" by(simp add: eqvt_def)

  from PSimQ have "(a<x>.P, a<x>.Q) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim P Q)
    thus ?case using \<open>eqvt ?X\<close>
      by(force intro: inputPres)
  next
    case(cSym P Q)
    thus ?case
      by(blast dest: symmetric)
  qed
qed

lemma outputPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<sim> Q"

  shows "a{b}.P \<sim> a{b}.Q"
proof -
  let ?X = "{(a{b}.P, a{b}.Q), (a{b}.Q, a{b}.P)}"
  have "(a{b}.P, a{b}.Q) \<in> ?X" by auto
  thus ?thesis using \<open>P \<sim> Q\<close>
    by(coinduct rule: bisimCoinduct)
      (auto intro: Strong_Late_Sim_Pres.outputPres dest: symmetric)
qed

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<sim> Q"

  shows "[a\<frown>b]P \<sim> [a\<frown>b]Q"
proof -
  let ?X = "{([a\<frown>b]P, [a\<frown>b]Q), ([a\<frown>b]Q, [a\<frown>b]P)}"
  have "([a\<frown>b]P, [a\<frown>b]Q) \<in> ?X" by auto
  thus ?thesis using \<open>P \<sim> Q\<close>
    by(coinduct rule: bisimCoinduct)
      (auto intro: Strong_Late_Sim_Pres.matchPres dest: symmetric bisimE)
qed

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<sim> Q"

  shows "[a\<noteq>b]P \<sim> [a\<noteq>b]Q"
proof -
  let ?X = "{([a\<noteq>b]P, [a\<noteq>b]Q), ([a\<noteq>b]Q, [a\<noteq>b]P)}"
  have "([a\<noteq>b]P, [a\<noteq>b]Q) \<in> ?X" by auto
  thus ?thesis using \<open>P \<sim> Q\<close>
    by(coinduct rule: bisimCoinduct)
      (auto intro: Strong_Late_Sim_Pres.mismatchPres dest: symmetric bisimE)
qed

lemma sumPres: 
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<sim> Q"

  shows "P \<oplus> R \<sim> Q \<oplus> R"
proof -
  let ?X = "{(P \<oplus> R, Q \<oplus> R), (Q \<oplus> R, P \<oplus> R)}"
  have "(P \<oplus> R, Q \<oplus> R) \<in> ?X" by auto
  thus ?thesis using \<open>P \<sim> Q\<close>
    by(coinduct rule: bisimCoinduct)
      (auto intro: Strong_Late_Sim_Pres.sumPres reflexive dest: symmetric bisimE)
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "P \<sim> Q"

  shows "<\<nu>x>P \<sim> <\<nu>x>Q"
proof -
  let ?X = "{x. \<exists>P Q. P \<sim> Q \<and> (\<exists>a. x = (<\<nu>a>P, <\<nu>a>Q))}"
  from \<open>P \<sim> Q\<close> have "(<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim xP xQ)
    {
      fix P Q a
      assume PSimQ: "P \<leadsto>[bisim] Q"
      moreover have "\<And>P Q a. P \<sim> Q \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> ?X \<union> bisim" by blast
      moreover have "bisim \<subseteq> ?X \<union> bisim" by blast
      moreover have "eqvt bisim" by simp
      moreover have "eqvt ?X"
        by(auto simp add: eqvt_def) (blast intro: bisimClosed)
      hence "eqvt (?X \<union> bisim)" by auto
      ultimately have "<\<nu>a>P \<leadsto>[(?X \<union> bisim)] <\<nu>a>Q"
        by(rule Strong_Late_Sim_Pres.resPres)
    }
    with \<open>(xP, xQ) \<in> ?X\<close> show ?case
      by(auto dest: bisimE)
  next
    case(cSym xP xQ)
    thus ?case by(auto dest: symmetric)
  qed
qed

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "P \<sim> Q"

  shows "P \<parallel> R \<sim> Q \<parallel> R"
proof -
  let ?X = "{(resChain lst (P \<parallel> R), resChain lst (Q \<parallel> R)) | lst P R Q. P \<sim> Q}"
  have EmptyChain: "\<And>P Q. P \<parallel> Q = resChain [] (P \<parallel> Q)" by auto
  with \<open>P \<sim> Q\<close> have "(P \<parallel> R, Q \<parallel> R) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim PR QR)
    {
      fix P Q R lst

      assume "P \<sim> Q"

      hence "P \<leadsto>[bisim] Q" by(rule bisimE)
      moreover note \<open>P \<sim> Q\<close>
      moreover have "\<And>P Q R. P \<sim> Q \<Longrightarrow> (P \<parallel> R, Q \<parallel> R) \<in> ?X"
        by auto (blast intro: EmptyChain)
      moreover 
      {
        fix xP xQ x
        assume "(xP, xQ) \<in> ?X"
        then obtain P Q R lst 
          where "P \<sim> Q" and "xP = resChain lst (P \<parallel> R)" and xQeq: "xQ = resChain lst (Q \<parallel> R)"
          by auto
        moreover hence "(resChain (x#lst) (P \<parallel> R), resChain (x#lst) (Q \<parallel> R)) \<in> ?X"
          by blast
        ultimately have "(<\<nu>x>xP, <\<nu>x>xQ) \<in> ?X" by auto
      }
      note ResPres = this
      moreover have "eqvt bisim" by simp
      moreover have "eqvt ?X"
        by(auto simp add: eqvt_def) (blast intro: bisimClosed)
      ultimately have "P \<parallel> R \<leadsto>[(?X)] Q \<parallel> R" by(rule parPres)
      hence "resChain lst (P \<parallel> R) \<leadsto>[?X] (resChain lst (Q \<parallel> R))" using \<open>eqvt ?X\<close> ResPres 
        by(rule resChainI)
      hence "resChain lst (P \<parallel> R) \<leadsto>[(?X \<union> bisim)] (resChain lst (Q \<parallel> R))"
        by(force intro: Strong_Late_Sim.monotonic)
    }
    with \<open>(PR, QR) \<in> ?X\<close> show ?case
      by auto
  next
    case(cSym PR QR)
    thus ?case by(blast dest: symmetric)
  qed
qed


lemma bangPres:
  fixes P :: pi
  and   Q :: pi

  assumes PBiSimQ: "P \<sim> Q"

  shows "!P \<sim> !Q"
proof -
  let ?X = "bangRel bisim"
  from PBiSimQ have "(!P, !Q) \<in> ?X" by(rule Rel.BRBang)
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim bP bQ)
    {
      fix P Q
      assume "(P, Q) \<in> ?X"
      hence "P \<leadsto>[?X] Q"
      proof(induct)
        fix P Q
        assume "P \<sim> Q"
        thus "!P \<leadsto>[?X] !Q" using bisimE bisimEqvt
          by(rule Strong_Late_Sim_Pres.bangPres)
      next
        fix P Q R T
        assume RBiSimT: "R \<sim> T"
        assume PBangRelQ: "(P, Q) \<in> ?X"
        assume PSimQ: "P \<leadsto>[?X] Q"
        from RBiSimT  have "R \<leadsto>[bisim] T" by(blast dest: bisimE)
        thus "R \<parallel> P \<leadsto>[?X] T \<parallel> Q" using PSimQ RBiSimT PBangRelQ Rel.BRPar Rel.BRRes bisimEqvt eqvtBangRel
          by(blast intro: Strong_Late_Sim_Pres.parCompose)
      next
        fix P Q a
        assume "P \<leadsto>[?X] Q"
        moreover from eqvtBangRel bisimEqvt have "eqvt ?X" by blast 
        ultimately show "<\<nu>a>P \<leadsto>[?X] <\<nu>a>Q" using Rel.BRRes by(blast intro: Strong_Late_Sim_Pres.resPres)
      qed
      hence "P \<leadsto>[((bangRel bisim) \<union> bisim)] Q" by(rule_tac Strong_Late_Sim.monotonic) auto
    }
    with \<open>(bP, bQ) \<in> ?X\<close> show ?case by auto
  next
    case(cSym bP bQ)
    thus ?case by(metis bangRelSymetric symmetric)
  qed
qed

end

