(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Bisim_Pres
  imports Strong_Bisim Strong_Sim_Pres
begin

lemma actPres:
  fixes P :: ccs
  and   Q :: ccs
  and   \<alpha> :: act

  assumes "P \<sim> Q"

  shows "\<alpha>.(P) \<sim> \<alpha>.(Q)"
proof -
  let ?X = "{(\<alpha>.(P), \<alpha>.(Q)) | P Q. P \<sim> Q}"
  from assms have "(\<alpha>.(P), \<alpha>.(Q)) \<in> ?X" by auto
  thus ?thesis 
    by(coinduct rule: bisimCoinduct) (auto dest: bisimE intro: actPres)
qed

lemma sumPres:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<sim> Q"

  shows "P \<oplus> R \<sim> Q \<oplus> R"
proof -
  let ?X = "{(P \<oplus> R, Q \<oplus> R) | P Q R. P \<sim> Q}"
  from assms have "(P \<oplus> R, Q \<oplus> R) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: sumPres reflexive dest: bisimE)
qed

lemma parPres:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<sim> Q"

  shows "P \<parallel> R \<sim> Q \<parallel> R"
proof -
  let ?X = "{(P \<parallel> R, Q \<parallel> R) | P Q R. P \<sim> Q}"
  from assms have "(P \<parallel> R, Q \<parallel> R) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: bisimCoinduct, auto) (blast intro: parPres dest: bisimE)+
qed

lemma resPres: 
  fixes P :: ccs
  and   Q :: ccs
  and   x :: name

  assumes "P \<sim> Q"

  shows "\<lparr>\<nu>x\<rparr>P \<sim> \<lparr>\<nu>x\<rparr>Q"
proof -
  let ?X = "{(\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) | x P Q. P \<sim> Q}"
  from assms have "(\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: bisimCoinduct) (auto intro: resPres dest: bisimE)
qed

lemma bangPres: 
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<sim> Q"

  shows "!P \<sim> !Q"
proof -
  from assms have "(!P, !Q) \<in> bangRel bisim"
    by(auto intro: BRBang)
  thus ?thesis
  proof(coinduct rule: bisimWeakCoinduct)
    case(cSim P Q)
    from `(P, Q) \<in> bangRel bisim` show ?case
    proof(induct)
      case(BRBang P Q)
      note `P \<sim> Q` bisimE(1)
      thus "!P \<leadsto>[bangRel bisim] !Q" by(rule bangPres)
    next
      case(BRPar R T P Q)
      from `R \<sim> T` have "R \<leadsto>[bisim] T" by(rule bisimE)
      moreover note `R \<sim> T` `P \<leadsto>[bangRel bisim] Q` `(P, Q) \<in> bangRel bisim` bangRel.BRPar
      ultimately show ?case by(rule Strong_Sim_Pres.parPresAux)
    qed
  next
    case(cSym P Q)
    thus ?case
      by induct (auto dest: bisimE intro: BRPar BRBang)
  qed
qed

end
