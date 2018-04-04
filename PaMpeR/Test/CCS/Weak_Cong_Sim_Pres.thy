(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Sim_Pres
  imports Weak_Cong_Sim
begin

lemma actPres:
  fixes P    :: ccs
  and   Q    :: ccs
  and   Rel  :: "(ccs \<times> ccs) set"
  and   a    :: name
  and   Rel' :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> Rel"

  shows "\<alpha>.(P) \<leadsto><Rel> \<alpha>.(Q)"
using assms
by(fastforce simp add: weakCongSimulation_def elim: actCases intro: weakCongAction)

lemma sumPres:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto><Rel> Q"
  and     "Rel \<subseteq> Rel'"
  and     "Id \<subseteq> Rel'"

  shows "P \<oplus> R \<leadsto><Rel'> Q \<oplus> R"
using assms
by(force simp add: weakCongSimulation_def elim: sumCases intro: weakCongSum1 weakCongSum2 transitionWeakCongTransition)

lemma parPres:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto><Rel> Q"
  and     "(P, Q) \<in> Rel"
  and     C1: "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"

  shows "P \<parallel> R \<leadsto><Rel'> Q \<parallel> R"
proof(induct rule: weakSimI)
  case(Sim \<alpha> QR)
  from `Q \<parallel> R \<longmapsto>\<alpha> \<prec> QR`
  show ?case
  proof(induct rule: parCases)
    case(cPar1 Q')
    from `P \<leadsto><Rel> Q` `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from `P \<Longrightarrow>\<alpha> \<prec> P'` have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<parallel> R" by(rule weakCongPar1)
    moreover from `(P', Q') \<in> Rel` have "(P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 R')
    from `R \<longmapsto>\<alpha> \<prec> R'` have "R \<Longrightarrow>\<alpha> \<prec> R'" by(rule transitionWeakCongTransition)
    hence "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P \<parallel> R'" by(rule weakCongPar2)
    moreover from `(P, Q) \<in> Rel` have "(P \<parallel> R', Q \<parallel> R') \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm Q' R' \<alpha>)
    from `P \<leadsto><Rel> Q` `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from `R \<longmapsto>(coAction \<alpha>) \<prec> R'` have "R \<Longrightarrow>(coAction \<alpha>) \<prec> R'"
      by(rule transitionWeakCongTransition)
    with `P \<Longrightarrow>\<alpha> \<prec> P'` have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" using `\<alpha> \<noteq> \<tau>` 
      by(rule weakCongSync)
    moreover from `(P', Q') \<in> Rel` have "(P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule C1)
    ultimately show ?case by blast
  qed
qed

lemma resPres:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   x   :: name

  assumes "P \<leadsto><Rel> Q"
  and     "\<And>R S y. (R, S) \<in> Rel \<Longrightarrow> (\<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows "\<lparr>\<nu>x\<rparr>P \<leadsto><Rel'> \<lparr>\<nu>x\<rparr>Q"
using assms
by(fastforce simp add: weakCongSimulation_def elim: resCases intro: weakCongRes)

lemma bangPres:
  fixes P    :: ccs
  and   Q    :: ccs
  and   Rel  :: "(ccs \<times> ccs) set"
  and   Rel' :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> Rel"
  and     C1: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel'> S"
  and     C2: "Rel \<subseteq> Rel'"

  shows "!P \<leadsto><bangRel Rel'> !Q"
proof(induct rule: weakSimI)
  case(Sim \<alpha> Q')
  {
    fix Pa \<alpha> Q'
    assume "!Q \<longmapsto>\<alpha> \<prec> Q'" and "(Pa, !Q) \<in> bangRel Rel"
    hence "\<exists>P'. Pa \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> bangRel Rel'"
    proof(nominal_induct arbitrary: Pa rule: bangInduct)
      case(cPar1 \<alpha> Q')
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel` 
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(P, Q) \<in> Rel` have "P \<leadsto><Rel'> Q" by(rule C1)
        with `Q \<longmapsto>\<alpha> \<prec> Q'` obtain P' where "P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel'"
          by(blast dest: weakSimE)
        from `P \<Longrightarrow>\<alpha> \<prec> P'` have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<parallel> R" by(rule weakCongPar1)
        moreover from `(R, !Q) \<in> bangRel Rel` C2 have "(R, !Q) \<in> bangRel Rel'"
          by induct (auto intro: bangRel.BRPar bangRel.BRBang)
        with `(P', Q') \<in> Rel'` have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel'"
          by(rule bangRel.BRPar)
        ultimately show ?case by blast
      qed
    next
      case(cPar2 \<alpha> Q')
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel`
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(R, !Q) \<in> bangRel Rel` obtain R' where "R \<Longrightarrow>\<alpha> \<prec> R'" and "(R', Q') \<in> bangRel Rel'" using cPar2
          by blast
        from `R \<Longrightarrow>\<alpha> \<prec> R'` have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P \<parallel> R'" by(rule weakCongPar2)
        moreover from `(P, Q) \<in> Rel` `(R', Q') \<in> bangRel Rel'` C2 have "(P \<parallel> R', Q \<parallel> Q') \<in> bangRel Rel'" 
          by(blast intro: bangRel.BRPar)
        ultimately show ?case by blast
      qed
    next
      case(cComm a Q' Q'' Pa)
      from `(Pa, Q \<parallel> !Q) \<in> bangRel Rel`
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from `(P, Q) \<in> Rel` have "P \<leadsto><Rel'> Q" by(rule C1)
        with `Q \<longmapsto>a \<prec> Q'` obtain P' where "P \<Longrightarrow>a \<prec> P'" and "(P', Q') \<in> Rel'"
          by(blast dest: weakSimE)
        from `(R, !Q) \<in> bangRel Rel` obtain R' where "R \<Longrightarrow>(coAction a) \<prec> R'" and "(R', Q'') \<in> bangRel Rel'" using cComm
          by blast
        from `P \<Longrightarrow>a \<prec> P'` `R \<Longrightarrow>(coAction a) \<prec> R'` `a \<noteq> \<tau>` have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" by(rule weakCongSync)
        moreover from `(P', Q') \<in> Rel'` `(R', Q'') \<in> bangRel Rel'` have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel'"
          by(rule bangRel.BRPar)
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
        then obtain P' where "P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> bangRel Rel'" using cBang
          by blast
        from `P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'` have "!P \<Longrightarrow>\<alpha> \<prec> P'" by(rule weakCongRepl)
        thus ?case using `(P', Q') \<in> bangRel Rel'` by blast
      qed
    qed
  }

  moreover from `(P, Q) \<in> Rel` have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?case using `!Q \<longmapsto> \<alpha> \<prec> Q'` by blast
qed

end
