(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Bisim_Pres
  imports Strong_Early_Bisim Strong_Early_Sim_Pres
begin

(************* Preservation rules *************)

lemma tauPres:
  fixes P :: pi
  and   Q :: pi

  assumes "P \<sim> Q"

  shows "\<tau>.(P) \<sim> \<tau>.(Q)"
proof -
  let ?X = "{(\<tau>.(P), \<tau>.(Q)) | P Q. P \<sim> Q}"
  from \<open>P \<sim> Q\<close> have "(\<tau>.(P), \<tau>.(Q)) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: tauPres dest: bisimE)
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
      by(blast dest: bisimE)
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
  let ?X = "{(a{b}.P, a{b}.Q) | a b P Q. P \<sim> Q}"
  from \<open>P \<sim> Q\<close> have "(a{b}.P, a{b}.Q) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (blast intro: outputPres dest: bisimE)+
qed

lemma matchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<sim> Q"

  shows "[a\<frown>b]P \<sim> [a\<frown>b]Q"
proof -
  let ?X = "{x. \<exists>P Q a b. P \<sim> Q \<and> x = ([a\<frown>b]P, [a\<frown>b]Q)}"
  from assms have "([a\<frown>b]P, [a\<frown>b]Q) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (blast intro: matchPres dest: bisimE)+
qed

lemma mismatchPres:
  fixes P :: pi
  and   Q :: pi
  and   a :: name
  and   b :: name

  assumes "P \<sim> Q"

  shows "[a\<noteq>b]P \<sim> [a\<noteq>b]Q"
proof -
  let ?X = "{x. \<exists>P Q a b. P \<sim> Q \<and> x = ([a\<noteq>b]P, [a\<noteq>b]Q)}"
  from assms have "([a\<noteq>b]P, [a\<noteq>b]Q) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (blast intro: mismatchPres dest: bisimE)+
qed

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "P \<sim> Q"

  shows "P \<oplus> R \<sim> Q \<oplus> R"
proof -
  let ?X = "{(P \<oplus> R, Q \<oplus> R) | P Q R. P \<sim> Q}"
  from assms have "(P \<oplus> R, Q \<oplus> R) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto dest: bisimE intro: reflexive sumPres)
qed

lemma resPres:
  fixes P :: pi
  and   Q :: pi
  and   x :: name
  
  assumes "P \<sim> Q"

  shows "<\<nu>x>P \<sim> <\<nu>x>Q"
proof -
  let ?X = "{x. \<exists>P Q. P \<sim> Q \<and> (\<exists>a. x = (<\<nu>a>P, <\<nu>a>Q))}"
  from assms have "(<\<nu>x>P, <\<nu>x>Q) \<in> ?X" by blast
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim xP xQ)
    moreover {
      fix P Q a
      assume "P \<sim> Q"
      hence "P \<leadsto>[bisim] Q" by(rule bisimE)
      moreover have "\<And>P Q a. P \<sim> Q \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> ?X \<union> bisim" by blast
      moreover have "bisim \<subseteq> ?X \<union> bisim" by blast
      moreover have "eqvt bisim" by(rule eqvt)
      moreover have "eqvt (?X \<union> bisim)" using eqvts
        by(auto simp add: eqvt_def) blast
      ultimately have "<\<nu>a>P \<leadsto>[(?X \<union> bisim)] <\<nu>a>Q"
        by(rule Strong_Early_Sim_Pres.resPres)
    }
    ultimately show ?case by auto
  next
    case(cSym xP xQ)
    thus ?case by(auto dest: bisimE)
  qed
qed

lemma parPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  and   T :: pi

  assumes "P \<sim> Q"

  shows "P \<parallel> R \<sim> Q \<parallel> R"
proof -
  let ?X = "{(resChain lst (P \<parallel> R), resChain lst (Q \<parallel> R)) | lst P Q R. P \<sim> Q}"
  have BC: "\<And>P Q. P \<parallel> Q = resChain [] (P \<parallel> Q)" by auto
  from assms have "(P \<parallel> R, Q \<parallel> R) \<in> ?X" by(blast intro: BC)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cSim PR QR)
    moreover {
      fix lst P Q R
      assume "P \<sim> Q"
      have "eqvt ?X" using eqvts by(auto simp add: eqvt_def) blast
      moreover have Res: "\<And>P Q x. (P, Q) \<in> ?X \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> ?X"
        by(auto, rule_tac x="x#lst" in exI) auto
      moreover {
        from \<open>P \<sim> Q\<close> have "P \<leadsto>[bisim] Q" by(rule bisimE)
        moreover note \<open>P \<sim> Q\<close>
        moreover have "\<And>P Q R. P \<sim> Q \<Longrightarrow> (P \<parallel> R, Q \<parallel> R) \<in> ?X"
          by(blast intro: BC)
        ultimately have "P \<parallel> R \<leadsto>[?X] Q \<parallel> R" using Res
          by(rule parPres)
      }

      ultimately have "resChain lst (P \<parallel> R) \<leadsto>[?X] resChain lst (Q \<parallel> R)"
        by(rule resChainI)
    }
    ultimately show ?case by auto
  next
    case(cSym P Q)
    thus ?case by(auto dest: bisimE)
  qed
qed

lemma bangRelBisimE: 
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes A:   "(P, Q) \<in> bangRel Rel"
  and     Sym: "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (Q, P) \<in> Rel"

  shows "(Q, P) \<in> bangRel Rel"
proof -
  from A show ?thesis
  proof(induct)
    fix P Q
    assume "(P, Q) \<in> Rel"
    hence "(Q, P) \<in> Rel" by(rule Sym)
    thus "(!Q, !P) \<in> bangRel Rel" by(rule BRBang)
  next
    fix P Q R T
    assume RRelT: "(R, T) \<in> Rel"
    assume IH: "(Q, P) \<in> bangRel Rel"
    from RRelT have "(T, R) \<in> Rel" by(rule Sym)
    thus "(T \<parallel> Q, R \<parallel> P) \<in> bangRel Rel" using IH by(rule BRPar)
  next
    fix P Q a
    assume "(Q, P) \<in> bangRel Rel"
    thus "(<\<nu>a>Q, <\<nu>a>P) \<in> bangRel Rel" by(rule BRRes)
  qed
qed

lemma bangPres:
  fixes P :: pi
  and   Q :: pi

  assumes PBiSimQ: "P \<sim> Q"

  shows "!P \<sim> !Q"
proof -
  let ?X = "bangRel bisim"
    from PBiSimQ have "(!P, !Q) \<in> ?X" by(rule BRBang)
    thus ?thesis
    proof(coinduct rule: bisimWeakCoinduct)
      case(cSim bP bQ)
      {
        fix P Q
        assume "(P, Q) \<in> ?X"
        hence "P \<leadsto>[?X] Q"
        proof(induct)
          fix P Q
          assume "P \<sim> Q"
          thus "!P \<leadsto>[?X] !Q" using bisimE(1) eqvt
            by(rule Strong_Early_Sim_Pres.bangPres)
        next
          fix P Q R T
          assume RBiSimT: "R \<sim> T"
          assume PBangRelQ: "(P, Q) \<in> ?X"
          assume PSimQ: "P \<leadsto>[?X] Q"
          from RBiSimT  have "R \<leadsto>[bisim] T" by(blast dest: bisimE)
          thus "R \<parallel> P \<leadsto>[?X] T \<parallel> Q" using PSimQ RBiSimT PBangRelQ BRPar BRRes eqvt eqvtBangRel
            by(blast intro: Strong_Early_Sim_Pres.parCompose)
        next
          fix P Q a
          assume "P \<leadsto>[?X] Q"
          moreover from eqvtBangRel eqvt have "eqvt ?X" by blast 
          ultimately show "<\<nu>a>P \<leadsto>[?X] <\<nu>a>Q" using BRRes by(blast intro: Strong_Early_Sim_Pres.resPres)
        qed
      }
      with \<open>(bP, bQ) \<in> ?X\<close> show ?case by blast
    next
      case(cSym bP bQ)
      thus ?case by(metis bangRelSymetric bisimE)
  qed
qed

end
