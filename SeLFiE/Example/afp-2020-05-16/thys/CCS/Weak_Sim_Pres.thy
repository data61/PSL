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
  from \<open>Q \<oplus> R \<longmapsto>\<alpha> \<prec> QR\<close> show ?case
  proof(induct rule: sumCases)
    case(cSum1 Q')
    from \<open>P \<leadsto>\<^sup>^<Rel> Q\<close> \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> 
    obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
      by(blast dest: weakSimE)
    thus ?case
    proof(induct rule: weakTransCases)
      case Base
      have "P \<oplus> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P \<oplus> R" by simp
      moreover from \<open>(P, Q') \<in> Rel\<close> have "(P \<oplus> R, Q') \<in> Rel'" by(rule C1)
      ultimately show ?case by blast
    next
      case Step
      from \<open>P \<Longrightarrow>\<alpha> \<prec> P'\<close> have "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> P'" by(rule weakCongSum1)
      hence "P \<oplus> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" by(simp add: weakTrans_def)
      thus ?case using \<open>(P', Q') \<in> Rel\<close> \<open>Rel \<subseteq> Rel'\<close> by blast
    qed
  next
    case(cSum2 R')
    from \<open>R \<longmapsto>\<alpha> \<prec> R'\<close> have "R \<Longrightarrow>\<alpha> \<prec> R'" by(rule transitionWeakCongTransition)
    hence "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> R'" by(rule weakCongSum2)
    hence "P \<oplus> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" by(simp add: weakTrans_def)
    thus ?case using \<open>Id \<subseteq> Rel'\<close> by blast
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
  from \<open>Q \<parallel> T \<longmapsto>\<alpha> \<prec> QT\<close>
  show ?case
  proof(induct rule: parCases)
    case(cPar1 Q')
    from \<open>P \<leadsto>\<^sup>^<Rel> Q\<close> \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from \<open>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'\<close> have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule weakPar1)
    moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R, T) \<in> Rel'\<close> have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    from \<open>R \<leadsto>\<^sup>^<Rel'> T\<close> \<open>T \<longmapsto>\<alpha> \<prec> T'\<close> obtain R' where "R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule weakSimE)
    from \<open>R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'\<close> have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule weakPar2)
    moreover from \<open>(P, Q) \<in> Rel\<close> \<open>(R', T') \<in> Rel'\<close> have "(P \<parallel> R', Q \<parallel> T') \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm Q' T' \<alpha>)
    from \<open>P \<leadsto>\<^sup>^<Rel> Q\<close> \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule weakSimE)
    from \<open>R \<leadsto>\<^sup>^<Rel'> T\<close> \<open>T \<longmapsto>(coAction \<alpha>) \<prec> T'\<close> obtain R' where "R \<Longrightarrow>\<^sup>^(coAction \<alpha>) \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule weakSimE)
    from \<open>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'\<close> \<open>R \<Longrightarrow>\<^sup>^(coAction \<alpha>) \<prec> R'\<close> \<open>\<alpha> \<noteq> \<tau>\<close> have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" 
      by(auto intro: weakCongSync simp add: weakTrans_def)
    hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'" by(simp add: weakTrans_def)
    moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R', T') \<in> Rel'\<close> have "(P' \<parallel> R', Q' \<parallel> T') \<in> Rel''" by(rule C1)
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
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close> 
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(P, Q) \<in> Rel\<close> have "P \<leadsto>\<^sup>^<Rel> Q" by(rule C1)
        with \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: weakSimE)
        from \<open>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'\<close> have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule weakPar1)
        moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R, !Q) \<in> bangRel Rel\<close> C2 have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> Rel'"
          by(blast intro: Par)
        ultimately show ?case by blast
      qed
    next
      case(cPar2 \<alpha> Q')
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close>
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(R, !Q) \<in> bangRel Rel\<close> obtain R' where "R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" and "(R', Q') \<in> Rel'" using cPar2
          by blast
        from \<open>R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'\<close> have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule weakPar2)
        moreover from \<open>(P, Q) \<in> Rel\<close> \<open>(R', Q') \<in> Rel'\<close> have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'" by(rule Par)
        ultimately show ?case by blast
      qed
    next
      case(cComm a Q' Q'' Pa)
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close>
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(P, Q) \<in> Rel\<close> have "P \<leadsto>\<^sup>^<Rel> Q" by(rule C1)
        with \<open>Q \<longmapsto>a \<prec> Q'\<close> obtain P' where "P \<Longrightarrow>\<^sup>^a \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: weakSimE)
        from \<open>(R, !Q) \<in> bangRel Rel\<close> obtain R' where "R \<Longrightarrow>\<^sup>^(coAction a) \<prec> R'" and "(R', Q'') \<in> Rel'" using cComm
          by blast
        from \<open>P \<Longrightarrow>\<^sup>^a \<prec> P'\<close> \<open>R \<Longrightarrow>\<^sup>^(coAction a) \<prec> R'\<close> \<open>a \<noteq> \<tau>\<close> have "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'"
          by(auto intro: weakCongSync simp add: weakTrans_def)
        moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R', Q'') \<in> Rel'\<close> have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> Rel'" by(rule Par)
        ultimately show ?case by blast
      qed
    next
      case(cBang \<alpha> Q' Pa)
      from \<open>(Pa, !Q) \<in> bangRel Rel\<close>
      show ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        from \<open>(P, Q) \<in> Rel\<close> have "(!P, !Q) \<in> bangRel Rel" by(rule bangRel.BRBang)
        with \<open>(P, Q) \<in> Rel\<close> have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule bangRel.BRPar)
        then obtain P' where "P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel'" using cBang
          by blast
        from \<open>P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'\<close> 
        show ?case
        proof(induct rule: weakTransCases)
          case Base
          have "!P \<Longrightarrow>\<^sup>^\<tau> \<prec> !P" by simp
          moreover from \<open>(P', Q') \<in> Rel'\<close> \<open>P \<parallel> !P = P'\<close> have "(!P, Q') \<in> Rel'" by(blast intro: C3)
          ultimately show ?case by blast
        next
          case Step
          from \<open>P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'\<close> have "!P \<Longrightarrow>\<alpha> \<prec> P'" by(rule weakCongRepl)
          hence "!P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" by(simp add: weakTrans_def)
          with \<open>(P', Q') \<in> Rel'\<close> show ?case by blast
        qed
      qed
    qed
  }

  moreover from \<open>(P, Q) \<in> Rel\<close> have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?case using \<open>!Q \<longmapsto> \<alpha> \<prec> Q'\<close> by blast
qed

end
