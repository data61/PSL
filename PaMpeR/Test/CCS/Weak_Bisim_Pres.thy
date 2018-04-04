(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Bisim_Pres
  imports Weak_Bisim Weak_Sim_Pres Strong_Bisim_SC
begin

lemma actPres:
  fixes P :: ccs
  and   Q :: ccs
  and   \<alpha> :: act

  assumes "P \<approx> Q"

  shows "\<alpha>.(P) \<approx> \<alpha>.(Q)"
proof -
  let ?X = "{(\<alpha>.(P), \<alpha>.(Q)) | P Q. P \<approx> Q}"
  from assms have "(\<alpha>.(P), \<alpha>.(Q)) \<in> ?X" by auto
  thus ?thesis 
    by(coinduct rule: weakBisimulationCoinduct) (auto dest: weakBisimulationE intro: actPres)
qed

lemma parPres:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "P \<approx> Q"

  shows "P \<parallel> R \<approx> Q \<parallel> R"
proof -
  let ?X = "{(P \<parallel> R, Q \<parallel> R) | P Q R. P \<approx> Q}"
  from assms have "(P \<parallel> R, Q \<parallel> R) \<in> ?X" by blast
  thus ?thesis
    by(coinduct rule: weakBisimulationCoinduct, auto) 
      (blast intro: parPres dest: weakBisimulationE)+
qed

lemma resPres: 
  fixes P :: ccs
  and   Q :: ccs
  and   x :: name

  assumes "P \<approx> Q"

  shows "\<lparr>\<nu>x\<rparr>P \<approx> \<lparr>\<nu>x\<rparr>Q"
proof -
  let ?X = "{(\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) | x P Q. P \<approx> Q}"
  from assms have "(\<lparr>\<nu>x\<rparr>P, \<lparr>\<nu>x\<rparr>Q) \<in> ?X" by auto
  thus ?thesis
    by(coinduct rule: weakBisimulationCoinduct) (auto intro: resPres dest: weakBisimulationE)
qed

lemma bangPres:
  fixes P :: ccs
  and   Q :: ccs

  assumes "P \<approx> Q"

  shows "!P \<approx> !Q"
proof -
  let ?X = "bangRel weakBisimulation"
  let ?Y = "weakBisimulation O ?X O bisim"
  {
    fix R T P Q
    assume "R \<approx> T" and "(P, Q) \<in> ?Y"
    from `(P, Q) \<in> ?Y` obtain P' Q' where "P \<approx> P'" and "(P', Q') \<in> ?X" and "Q' \<sim> Q"
      by auto
    from `P \<approx> P'` have "R \<parallel> P \<approx> R \<parallel> P'" 
      by(metis parPres bisimWeakBisimulation transitive parComm)
    moreover from `R \<approx> T` `(P', Q') \<in> ?X` have "(R \<parallel> P', T \<parallel> Q') \<in> ?X" by(auto dest: BRPar)
    moreover from `Q' \<sim> Q` have "T \<parallel> Q' \<sim> T \<parallel> Q" by(metis Strong_Bisim_Pres.parPres Strong_Bisim.transitive parComm)
    ultimately have "(R \<parallel> P, T \<parallel> Q) \<in> ?Y" by auto
  } note BRParAux = this

  from assms have "(!P, !Q) \<in> ?X" by(auto intro: BRBang)
  thus ?thesis
  proof(coinduct rule: weakBisimWeakUpto)
    case(cSim P Q)
    from `(P, Q) \<in> bangRel weakBisimulation` show ?case
    proof(induct)
      case(BRBang P Q)
      note `P \<approx> Q` weakBisimulationE(1) BRParAux
      moreover have "?X \<subseteq> ?Y" by(auto intro: Strong_Bisim.reflexive reflexive)
      moreover {
        fix P Q
        assume "(P \<parallel> !P, Q) \<in> ?Y"
        hence "(!P, Q) \<in> ?Y" using bangUnfold
          by(blast dest: Strong_Bisim.transitive transitive bisimWeakBisimulation)
      }
      ultimately show ?case by(rule bangPres)
    next
      case(BRPar R T P Q)
      from `R \<approx> T` have "R \<leadsto>\<^sup>^<weakBisimulation> T" by(rule weakBisimulationE)
      moreover note `R \<approx> T` `P \<leadsto>\<^sup>^<?Y> Q` 
      moreover from `(P, Q) \<in> ?X` have "(P, Q) \<in> ?Y" by(blast intro: Strong_Bisim.reflexive reflexive)
      ultimately show ?case using BRParAux by(rule Weak_Sim_Pres.parPresAux)
    qed
  next
    case(cSym P Q)
    thus ?case
      by induct (auto dest: weakBisimulationE intro: BRPar BRBang)
  qed
qed

end

