(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Sim_Pres
  imports Weak_Sim
begin

lemma actPres:
  fixes P    :: ccs
  and   Q    :: ccs
  and   Rel  :: "(ccs \<times> ccs) set"
  and   a    :: name
  and   Rel' :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> Rel"

  shows "\<alpha>.(P) \<leadsto>\<^sup>^<Rel> \<alpha>.(Q)"
using assms
by(fastforce simp add: weakSimulation_def elim: actCases intro: weakAction)

lemma sumPres:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "Rel \<subseteq> Rel'"
  and     "Id \<subseteq> Rel'"
  and     C1: "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<oplus> U, T) \<in> Rel'"

  shows "P \<oplus> R \<leadsto>\<^sup>^<Rel'> Q \<oplus> R"
proof(induct rule: weakSimI)
  case(Sim \<alpha> QR)
  from `Q \<oplus> R \<longmapsto>\<alpha> \<prec> QR` show ?case
  proof(induct rule: sumCases)
    case(cSum1 Q')
    from `P \<leadsto>\<^sup>^<Rel> Q` `Q \<longmapsto>\<alpha> \<prec> Q'` 
    obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
      by(blast dest: weakSimE)
    thus ?case
    proof(induct rule: weakTransCases)
      case Base
      have "P \<oplus> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P \<oplus> R" by simp
      moreover from `(P, Q') \<in> Rel` have "(P \<oplus> R, Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    next
      case Step
      from `P \<Longrightarrow>\<alpha> \<prec> P'` have "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> P'" by(rule weakCongSum1)
      hence "P \<oplus> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" by(simp add: weakTrans_def)
      thus ?case using `(P', Q') \<in> Rel` `Rel \<subseteq> Rel'` by blast
    qed
  next
    case(cSum2 R')
    from `R \<longmapsto>\<alpha> \<prec> R'` have "R \<Longrightarrow>\<alpha> \<prec> R'" by(rule transitionWeakCongTransition)
    hence "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> R'" by(rule weakCongSum2)
    hence "P \<oplus> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" by(simp add: weakTrans_def)
    thus ?case using `Id \<subseteq> Rel'` by blast
  qed
qed

lemma parPresAux:
  fixes P     :: ccs
  and   Q     :: ccs
  and   R     :: ccs
  and   T     :: ccs
  and   Rel   :: "(ccs \<times> ccs) set"
  and   Rel'  :: "(ccs \<times> ccs) set"
  and   Rel'' :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "(P, Q) \<in> Rel"
  and     "R \<leadsto>\<^sup>^<Rel'> T"
  and     "(R, T) \<in> Rel'"
  and     C1: "\<And>P' Q' R' T'. \<lbrakk>(P', Q') \<in> Rel; (R', T') \<in> Rel'\<rbrakk> \<Longrightarrow> (P' \<parallel> R', Q' \<parallel> T') \<in> Rel''"

  shows "P \<parallel> R \<leadsto>\<^sup>^<Rel''> Q \<parallel> T"
proof(induct rule: weakSimI)
  case(Sim \<alpha> QT)
  from `Q \<parallel> T \<longmapsto>\<alpha> \<prec> QT`
  show ?case
  proof(induct rule: parCases)
    case(cPar1 Q')
    from `P \<leadsto>\<^sup>^<Rel> Q` `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from `P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'` have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule weakPar1)
    moreover from `(P', Q') \<in> Rel` `(R, T) \<in> Rel'` have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    from `R \<leadsto>\<^sup>^<Rel'> T` `T \<longmapsto>\<alpha> \<prec> T'` obtain R' where "R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule weakSimE)
    from `R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'` have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule weakPar2)
    moreover from `(P, Q) \<in> Rel` `(R', T') \<in> Rel'` have "(P \<parallel> R', Q \<parallel> T') \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm Q' T' \<alpha>)
    from `P \<leadsto>\<^sup>^<Rel> Q` `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from `R \<leadsto>\<^sup>^<Rel'> T` `T \<longmapsto>(coAction \<alpha>) \<prec> T'` obtain R' where "R \<Longrightarrow>\<^sup>^(coAction \<alpha>) \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule weakSimE)
    from `P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'` `R \<Longrightarrow>\<^sup>^(coAction \<alpha>) \<prec> R'` `\<alpha> \<noteq> \<tau>` have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" 
      by(auto intro: weakCongSync simp add: weakTrans_def)
    hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'" by(simp add: weakTrans_def)
    moreover from `(P', Q') \<in> Rel` `(R', T') \<in> Rel'` have "(P' \<parallel> R', Q' \<parallel> T') \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  qed
qed

lemma parPres:
  fixes P    :: ccs
  and   Q    :: ccs
  and   R    :: ccs
  and   Rel  :: "(ccs \<times> ccs) set"
  and   Rel' :: "(ccs \<times> ccs) set"
  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "(P, Q) \<in> Rel"
  and     C1: "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"

  shows "P \<parallel> R \<leadsto>\<^sup>^<Rel'> Q \<parallel> R"
using assms
by(rule_tac parPresAux[where Rel'=Id and Rel''=Rel']) (auto intro: reflexive)

lemma resPres:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   x   :: name

  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "\<And>R S y. (R, S) \<in> Rel \<Longrightarrow> (\<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows "\<lparr>\<nu>x\<rparr>P \<leadsto>\<^sup>^<Rel'> \<lparr>\<nu>x\<rparr>Q"
using assms
by(fastforce simp add: weakSimulation_def elim: resCases intro: weakRes)

lemma bangPres:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "(P, Q) \<in> Rel"
  and     C1: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S"
  and     Par: "\<And>R S T U. \<lbrakk>(R, S) \<in> Rel; (T, U) \<in> Rel'\<rbrakk> \<Longrightarrow> (R \<parallel> T, S \<parallel> U) \<in> Rel'"
  and     C2: "bangRel Rel \<subseteq> Rel'"
  and     C3: "\<And>R S. (R \<parallel> !R, S) \<in> Rel' \<Longrightarrow> (!R, S) \<in> Rel'"

  shows "!P \<leadsto>\<^sup>^<Rel'> !Q"
proof(induct rule: weakSimI)
  case(Sim \<alpha> Q')
  {
    fix Pa \<alpha> Q'
    assume "!Q \<longmapsto>\<alpha> \<prec> Q'" and "(Pa, !Q) \<in> bangRel Rel"
    hence "\<exists>P'. Pa \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
    proof(nominal_induct arbitrary: Pa rule: bangInduct)
      case(cPar1 \<alpha> Q')
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel` 
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(P, Q) \<in> Rel` have "P \<leadsto>\<^sup>^<Rel> Q" by(rule C1)
        with `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: weakSimE)
        from `P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'` have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule weakPar1)
        moreover from `(P', Q') \<in> Rel` `(R, !Q) \<in> bangRel Rel` C2 have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> Rel'"
          by(blast intro: Par)
        ultimately show ?case by blast
      qed
    next
      case(cPar2 \<alpha> Q')
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel`
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(R, !Q) \<in> bangRel Rel` obtain R' where "R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" and "(R', Q') \<in> Rel'" using cPar2
          by blast
        from `R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'` have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule weakPar2)
        moreover from `(P, Q) \<in> Rel` `(R', Q') \<in> Rel'` have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'" by(rule Par)
        ultimately show ?case by blast
      qed
    next
      case(cComm a Q' Q'' Pa)
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel`
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(P, Q) \<in> Rel` have "P \<leadsto>\<^sup>^<Rel> Q" by(rule C1)
        with `Q \<longmapsto>a \<prec> Q'` obtain P' where "P \<Longrightarrow>\<^sup>^a \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: weakSimE)
        from `(R, !Q) \<in> bangRel Rel` obtain R' where "R \<Longrightarrow>\<^sup>^(coAction a) \<prec> R'" and "(R', Q'') \<in> Rel'" using cComm
          by blast
        from `P \<Longrightarrow>\<^sup>^a \<prec> P'` `R \<Longrightarrow>\<^sup>^(coAction a) \<prec> R'` `a \<noteq> \<tau>` have "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'"
          by(auto intro: weakCongSync simp add: weakTrans_def)
        moreover from `(P', Q') \<in> Rel` `(R', Q'') \<in> Rel'` have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> Rel'" by(rule Par)
        ultimately show ?case by blast
      qed
    next
      case(cBang \<alpha> Q' Pa)
      from `(Pa, !Q) \<in> bangRel Rel`
      show ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        from `(P, Q) \<in> Rel` have "(!P, !Q) \<in> bangRel Rel" by(rule bangRel.BRBang)
        with `(P, Q) \<in> Rel` have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule bangRel.BRPar)
        then obtain P' where "P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel'" using cBang
          by blast
        from `P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'` 
        show ?case
        proof(induct rule: weakTransCases)
          case Base
          have "!P \<Longrightarrow>\<^sup>^\<tau> \<prec> !P" by simp
          moreover from `(P', Q') \<in> Rel'` `P \<parallel> !P = P'` have "(!P, Q') \<in> Rel'" by(blast intro: C3)
          ultimately show ?case by blast
        next
          case Step
          from `P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'` have "!P \<Longrightarrow>\<alpha> \<prec> P'" by(rule weakCongRepl)
          hence "!P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" by(simp add: weakTrans_def)
          with `(P', Q') \<in> Rel'` show ?case by blast
        qed
      qed
    qed
  }

  moreover from `(P, Q) \<in> Rel` have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?case using `!Q \<longmapsto> \<alpha> \<prec> Q'` by blast
qed

end
