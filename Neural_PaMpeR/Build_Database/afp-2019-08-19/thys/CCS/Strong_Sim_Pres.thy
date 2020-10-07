(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Sim_Pres
  imports Strong_Sim
begin

lemma actPres:
  fixes P    :: ccs
  and   Q    :: ccs
  and   Rel  :: "(ccs \<times> ccs) set"
  and   a    :: name
  and   Rel' :: "(ccs \<times> ccs) set"

  assumes "(P, Q) \<in> Rel"

  shows "\<alpha>.(P) \<leadsto>[Rel] \<alpha>.(Q)"
using assms
by(fastforce simp add: simulation_def elim: actCases intro: Action)

lemma sumPres:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>[Rel] Q"
  and     "Rel \<subseteq> Rel'"
  and     "Id \<subseteq> Rel'"

  shows "P \<oplus> R \<leadsto>[Rel'] Q \<oplus> R"
using assms
by(force simp add: simulation_def elim: sumCases intro: Sum1 Sum2)

lemma parPresAux:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>[Rel] Q"
  and     "(P, Q) \<in> Rel"
  and     "R \<leadsto>[Rel'] T"
  and     "(R, T) \<in> Rel'"
  and     C1: "\<And>P' Q' R' T'. \<lbrakk>(P', Q') \<in> Rel; (R', T') \<in> Rel'\<rbrakk> \<Longrightarrow> (P' \<parallel> R', Q' \<parallel> T') \<in> Rel''"

  shows "P \<parallel> R \<leadsto>[Rel''] Q \<parallel> T"
proof(induct rule: simI)
  case(Sim a QT)
  from \<open>Q \<parallel> T \<longmapsto>a \<prec> QT\<close>
  show ?case
  proof(induct rule: parCases)
    case(cPar1 Q')
    from \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto>a \<prec> Q'\<close> obtain P' where "P \<longmapsto>a \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule simE)
    from \<open>P \<longmapsto>a \<prec> P'\<close> have "P \<parallel> R \<longmapsto>a \<prec> P' \<parallel> R" by(rule Par1)
    moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R, T) \<in> Rel'\<close> have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    from \<open>R \<leadsto>[Rel'] T\<close> \<open>T \<longmapsto>a \<prec> T'\<close> obtain R' where "R \<longmapsto>a \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule simE)
    from \<open>R \<longmapsto>a \<prec> R'\<close> have "P \<parallel> R \<longmapsto>a \<prec> P \<parallel> R'" by(rule Par2)
    moreover from \<open>(P, Q) \<in> Rel\<close> \<open>(R', T') \<in> Rel'\<close> have "(P \<parallel> R', Q \<parallel> T') \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  next
    case(cComm Q' T' a)
    from \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto>a \<prec> Q'\<close> obtain P' where "P \<longmapsto>a \<prec> P'" and "(P', Q') \<in> Rel" 
      by(rule simE)
    from \<open>R \<leadsto>[Rel'] T\<close> \<open>T \<longmapsto>(coAction a) \<prec> T'\<close> obtain R' where "R \<longmapsto>(coAction a) \<prec> R'" and "(R', T') \<in> Rel'" 
      by(rule simE)
    from \<open>P \<longmapsto>a \<prec> P'\<close> \<open>R \<longmapsto>(coAction a) \<prec> R'\<close> \<open>a \<noteq> \<tau>\<close> have "P \<parallel> R \<longmapsto>\<tau> \<prec> P' \<parallel> R'" by(rule Comm)
    moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R', T') \<in> Rel'\<close> have "(P' \<parallel> R', Q' \<parallel> T') \<in> Rel''" by(rule C1)
    ultimately show ?case by blast
  qed
qed

lemma parPres:
  fixes P   :: ccs
  and   Q   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>[Rel] Q"
  and     "(P, Q) \<in> Rel"
  and     C1: "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"

  shows "P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
using assms
by(rule_tac parPresAux[where Rel''=Rel' and Rel'=Id]) (auto intro: reflexive)

lemma resPres:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   x   :: name

  assumes "P \<leadsto>[Rel] Q"
  and     "\<And>R S y. (R, S) \<in> Rel \<Longrightarrow> (\<lparr>\<nu>y\<rparr>R, \<lparr>\<nu>y\<rparr>S) \<in> Rel'"

  shows "\<lparr>\<nu>x\<rparr>P \<leadsto>[Rel'] \<lparr>\<nu>x\<rparr>Q"
using assms
by(fastforce simp add: simulation_def elim: resCases intro: Res)

lemma bangPres:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "(P, Q) \<in> Rel"
  and     C1: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>[Rel] S"

  shows "!P \<leadsto>[bangRel Rel] !Q"
proof(induct rule: simI)
  case(Sim \<alpha> Q')
  {
    fix Pa \<alpha> Q'
    assume "!Q \<longmapsto>\<alpha> \<prec> Q'" and "(Pa, !Q) \<in> bangRel Rel"
    hence "\<exists>P'. Pa \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> bangRel Rel"
    proof(nominal_induct arbitrary: Pa rule: bangInduct)
      case(cPar1 \<alpha> Q')
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close> 
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(P, Q) \<in> Rel\<close> have "P \<leadsto>[Rel] Q" by(rule C1)
        with \<open>Q \<longmapsto>\<alpha> \<prec> Q'\<close> obtain P' where "P \<longmapsto>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: simE)
        from \<open>P \<longmapsto>\<alpha> \<prec> P'\<close> have "P \<parallel> R \<longmapsto>\<alpha> \<prec> P' \<parallel> R" by(rule Par1)
        moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R, !Q) \<in> bangRel Rel\<close> have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel"
          by(rule bangRel.BRPar)
        ultimately show ?case by blast
      qed
    next
      case(cPar2 \<alpha> Q')
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close>
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(R, !Q) \<in> bangRel Rel\<close> obtain R' where "R \<longmapsto>\<alpha> \<prec> R'" and "(R', Q') \<in> bangRel Rel" using cPar2
          by blast
        from \<open>R \<longmapsto>\<alpha> \<prec> R'\<close> have "P \<parallel> R \<longmapsto>\<alpha> \<prec> P \<parallel> R'" by(rule Par2)
        moreover from \<open>(P, Q) \<in> Rel\<close> \<open>(R', Q') \<in> bangRel Rel\<close> have "(P \<parallel> R', Q \<parallel> Q') \<in> bangRel Rel" by(rule bangRel.BRPar)
        ultimately show ?case by blast
      qed
    next
      case(cComm a Q' Q'' Pa)
      from \<open>(Pa, Q \<parallel> !Q) \<in> bangRel Rel\<close>
      show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        from \<open>(P, Q) \<in> Rel\<close> have "P \<leadsto>[Rel] Q" by(rule C1)
        with \<open>Q \<longmapsto>a \<prec> Q'\<close> obtain P' where "P \<longmapsto>a \<prec> P'" and "(P', Q') \<in> Rel"
          by(blast dest: simE)
        from \<open>(R, !Q) \<in> bangRel Rel\<close> obtain R' where "R \<longmapsto>(coAction a) \<prec> R'" and "(R', Q'') \<in> bangRel Rel" using cComm
          by blast
        from \<open>P \<longmapsto>a \<prec> P'\<close> \<open>R \<longmapsto>(coAction a) \<prec> R'\<close> \<open>a \<noteq> \<tau>\<close> have "P \<parallel> R \<longmapsto>\<tau> \<prec> P' \<parallel> R'" by(rule Comm)
        moreover from \<open>(P', Q') \<in> Rel\<close> \<open>(R', Q'') \<in> bangRel Rel\<close> have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel" by(rule bangRel.BRPar)
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
        then obtain P' where "P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'" and "(P', Q') \<in> bangRel Rel" using cBang
          by blast
        from \<open>P \<parallel> !P \<longmapsto>\<alpha> \<prec> P'\<close> have "!P \<longmapsto>\<alpha> \<prec> P'" by(rule Bang)
        thus ?case using \<open>(P', Q') \<in> bangRel Rel\<close> by blast
      qed
    qed
  }

  moreover from \<open>(P, Q) \<in> Rel\<close> have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?case using \<open>!Q \<longmapsto> \<alpha> \<prec> Q'\<close> by blast
qed

end
