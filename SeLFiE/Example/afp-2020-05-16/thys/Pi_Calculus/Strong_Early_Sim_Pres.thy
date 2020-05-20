(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Sim_Pres
  imports Strong_Early_Sim
begin

lemma tauPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "\<tau>.(P) \<leadsto>[Rel] \<tau>.(Q)"
proof(induct rule: simCases)
  case(Bound a y Q')
  have "\<tau>.(Q) \<longmapsto> a<\<nu>y> \<prec> Q'" by fact
  hence False by(induct rule: tauCases', auto)
  thus ?case by simp
next
  case(Free \<alpha> Q')
  have "\<tau>.(Q) \<longmapsto> \<alpha> \<prec> Q'" by fact
  thus "\<exists>P'. \<tau>.(P) \<longmapsto> \<alpha>  \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: tauCases', auto simp add: pi.inject residual.inject)
    have "\<tau>.(P) \<longmapsto> \<tau> \<prec> P" by(rule TransitionsEarly.Tau)
    with PRelQ show "\<exists>P'. \<tau>.(P) \<longmapsto> \<tau> \<prec> P' \<and> (P', Q) \<in> Rel" by blast
  qed
qed


lemma inputPres:
  fixes P    :: pi
  and   x    :: name
  and   Q    :: pi
  and   a    :: name
  and   Rel  :: "(pi \<times> pi) set"

  assumes PRelQ: "\<forall>y. (P[x::=y], Q[x::=y]) \<in> Rel"
  and     Eqvt: "eqvt Rel"

  shows "a<x>.P \<leadsto>[Rel] a<x>.Q"
using Eqvt
proof(induct rule: simCasesCont[where C="(x, a, P, Q)"])
  case(Bound b y Q')
  from \<open>y \<sharp> (x, a, P, Q)\<close> have "y \<noteq> x" "y \<noteq> a" "y \<sharp> P" "y \<sharp> Q" by simp+
  from \<open>a<x>.Q \<longmapsto>b<\<nu>y> \<prec> Q'\<close> \<open>y \<noteq> a\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close> show ?case
    by(erule_tac inputCases') auto
next
  case(Free \<alpha> Q')
  from \<open>a<x>.Q \<longmapsto> \<alpha> \<prec> Q'\<close>
  show ?case
  proof(induct rule: inputCases)
    case(cInput u)
    have "a<x>.P \<longmapsto>a<u> \<prec> P[x::=u]" by(rule Input)
    moreover from PRelQ have "(P[x::=u], Q[x::=u]) \<in> Rel" by auto
    ultimately show ?case by blast
  qed
qed

lemma outputPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "a{b}.P \<leadsto>[Rel] a{b}.Q"
proof(induct rule: simCases)
  case(Bound c y Q')
  have "a{b}.Q \<longmapsto> c<\<nu>y> \<prec> Q'" by fact
  hence False by(induct rule: outputCases', auto)
  thus "\<exists>P'. a{b}.P \<longmapsto> c<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel" by simp
next
  case(Free \<alpha> Q')
  have "a{b}.Q \<longmapsto> \<alpha> \<prec> Q'" by fact
  thus "\<exists>P'. a{b}.P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: outputCases', auto simp add: pi.inject residual.inject)
    have "a{b}.P \<longmapsto> a[b] \<prec> P" by(rule TransitionsEarly.Output)
    with PRelQ show "\<exists>P'. a{b}.P \<longmapsto> a[b] \<prec> P' \<and> (P', Q) \<in> Rel" by blast
  qed
qed

lemma matchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  shows "[a\<frown>b]P \<leadsto>[Rel'] [a\<frown>b]Q"
proof(induct rule: simCases)
  case(Bound c y Q')
  have "(y::name) \<sharp> [a\<frown>b]P" by fact
  hence yFreshP: "y \<sharp> P" by simp
  have "[a\<frown>b]Q \<longmapsto> c<\<nu>y> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case Match
    have "Q \<longmapsto>c<\<nu>y> \<prec> Q'" by fact
    with PSimQ yFreshP obtain P' where PTrans: "P \<longmapsto>c<\<nu>y> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)
    
    from PTrans have "[a\<frown>a]P \<longmapsto> c<\<nu>y> \<prec> P'" by(rule Early_Semantics.Match)
    moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> Q')
  assume "[a\<frown>b]Q \<longmapsto> \<alpha> \<prec> Q'"
  thus ?case
  proof(induct rule: matchCases)
    case Match
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)

    from PTrans have "[a\<frown>a]P \<longmapsto>\<alpha> \<prec> P'" by(rule TransitionsEarly.Match)
    moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed

lemma mismatchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     RelRel': "Rel \<subseteq> Rel'"

  shows "[a\<noteq>b]P \<leadsto>[Rel'] [a\<noteq>b]Q"
proof(cases "a = b")
  assume "a = b"
  thus ?thesis
    by(auto simp add: strongSimEarly_def)
next
  assume aineqb: "a \<noteq> b"
  show ?thesis
  proof(induct rule: simCases)
    case(Bound c x Q')
    have "x \<sharp> [a\<noteq>b]P" by fact
    hence xFreshP: "x \<sharp> P" by simp
    have "[a\<noteq>b]Q \<longmapsto> c<\<nu>x> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: mismatchCases)
      case Mismatch
      have "Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
      with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>c<\<nu>x> \<prec> P'"
                                     and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: elim)

      from PTrans aineqb have "[a\<noteq>b]P \<longmapsto> c<\<nu>x> \<prec> P'" by(rule Early_Semantics.Mismatch)
      moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
      ultimately show ?case by blast
    qed
  next
    case(Free \<alpha> Q')
    have "[a\<noteq>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: mismatchCases)
      case Mismatch
      have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'"
                             and PRel: "(P', Q') \<in> Rel"
          by(blast dest: elim)
      from PTrans \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<longmapsto>\<alpha> \<prec> P'" by(rule TransitionsEarly.Mismatch)
      with RelRel' PRel show ?case by blast
    qed
  qed
qed

lemma sumPres:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"

  assumes "P \<leadsto>[Rel] Q"
  and     C1: "Id \<subseteq> Rel'"
  and     "Rel \<subseteq> Rel'"

  shows "P \<oplus> R \<leadsto>[Rel'] Q \<oplus> R"
proof(induct rule: simCases)
  case(Bound a y Q')
  have "y \<sharp> P \<oplus> R" by fact
  hence "(y::name) \<sharp> P" and  "y \<sharp> R" by simp+
  from \<open>Q \<oplus> R \<longmapsto>a<\<nu>y> \<prec> Q'\<close> show ?case
  proof(induct rule: sumCases)
    case Sum1
    from \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto>a<\<nu>y> \<prec> Q'\<close> \<open>y \<sharp> P\<close> obtain P' where PTrans: "P \<longmapsto>a<\<nu>y> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)
    
    from PTrans have "P \<oplus> R \<longmapsto>a<\<nu>y> \<prec> P'" by(rule Early_Semantics.Sum1)
    moreover from P'RelQ' \<open>Rel \<subseteq> Rel'\<close> have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  next
    case Sum2
    from \<open>R \<longmapsto>a<\<nu>y> \<prec> Q'\<close> have "P \<oplus> R \<longmapsto>a<\<nu>y> \<prec> Q'" by(rule Early_Semantics.Sum2)
    moreover from C1 have "(Q', Q') \<in> Rel'" by auto
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> Q')
  from \<open>Q \<oplus> R \<longmapsto>\<alpha> \<prec> Q'\<close> show "\<exists>P'. P \<oplus> R \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
  proof(induct rule: sumCases)
    case Sum1
    have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    with \<open>P \<leadsto>[Rel] Q\<close> obtain P' where PTrans: "P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)

    from PTrans have "P \<oplus> R \<longmapsto>\<alpha> \<prec> P'" by(rule TransitionsEarly.Sum1)
    moreover from P'RelQ' \<open>Rel \<subseteq> Rel'\<close> have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  next
    case Sum2
    from \<open>R \<longmapsto>\<alpha> \<prec> Q'\<close> have "P \<oplus> R \<longmapsto>\<alpha> \<prec> Q'" by(rule TransitionsEarly.Sum2)
    moreover from C1 have "(Q', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed

lemma parCompose:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   T     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"
  
  assumes PSimQ:    "P \<leadsto>[Rel] Q"
  and     RSimT:    "R \<leadsto>[Rel'] S"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     RRel'T:   "(R, S) \<in> Rel'"
  and     Par:      "\<And>P' Q' R' S'. \<lbrakk>(P', Q') \<in> Rel; (R', S') \<in> Rel'\<rbrakk> \<Longrightarrow> (P' \<parallel> R', Q' \<parallel> S') \<in> Rel''"
  and     Res:      "\<And>S T x. (S, T) \<in> Rel'' \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel''"

  shows "P \<parallel> R \<leadsto>[Rel''] Q \<parallel> S"
proof(induct rule: simCases)
  case(Bound a x Q')
  have "x \<sharp> P \<parallel> R" by fact
  hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
  have "Q \<parallel> S \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    have "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact      
    with PSimQ xFreshP obtain P' where PTrans:"P \<longmapsto> a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)

    from PTrans xFreshR have "P \<parallel> R \<longmapsto> a<\<nu>x> \<prec> (P' \<parallel> R)" by(rule Early_Semantics.Par1B)
    moreover from P'RelQ' RRel'T have "(P' \<parallel> R, Q' \<parallel> S) \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cPar2 S')
    have "S \<longmapsto> a<\<nu>x> \<prec> S'" by fact
    with RSimT xFreshR obtain R' where RTrans:"R \<longmapsto> a<\<nu>x> \<prec> R'" and R'Rel'T': "(R', S') \<in>  Rel'" 
      by(blast dest: elim)

    from RTrans xFreshP have ParTrans: "P \<parallel> R \<longmapsto> a<\<nu>x> \<prec> (P \<parallel> R')" by(rule Early_Semantics.Par2B)
    moreover from PRelQ R'Rel'T' have "(P \<parallel> R', Q \<parallel>  S') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> QT')
  have "Q \<parallel> S \<longmapsto> \<alpha> \<prec> QT'" by fact
  thus ?case
  proof(induct rule: parCasesF[of _ _ _ _ _ "(P, R)"])
    case(cPar1 Q')
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel" 
      by(blast dest: elim)

    from PTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<parallel> R" by(rule Early_Semantics.Par1F)
    moreover from PRel RRel'T have "(P' \<parallel> R, Q' \<parallel> S) \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cPar2 S')
    have "S \<longmapsto> \<alpha> \<prec> S'" by fact
    with RSimT obtain R' where RTrans: "R \<longmapsto> \<alpha> \<prec> R'" and RRel: "(R', S') \<in> Rel'" 
      by(blast dest: elim)

    from RTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P \<parallel> R'" by(rule Early_Semantics.Par2F)
    moreover from PRelQ RRel have "(P \<parallel> R', Q \<parallel> S') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cComm1 Q' S' a b)
    have "Q \<longmapsto> a<b> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto>a<b> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: elim)
    
    have "S \<longmapsto> a[b] \<prec> S'" by fact
    with RSimT obtain R' where RTrans: "R \<longmapsto>a[b] \<prec> R'" and RRel: "(R', S') \<in> Rel'"
      by(blast dest: elim)
    
    from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<parallel> R'" by(rule Early_Semantics.Comm1)
    moreover from P'RelQ' RRel have "(P' \<parallel> R', Q' \<parallel> S') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cComm2 Q' S' a b)
    have "Q \<longmapsto> (OutputR a b) \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto>a[b] \<prec> P'" and PRel: "(P', Q') \<in> Rel" 
      by(blast dest: elim)
    
    have "S \<longmapsto> a<b> \<prec> S'" by fact
    with RSimT obtain R' where RTrans: "R \<longmapsto>a<b> \<prec> R'" and R'Rel'T': "(R', S') \<in> Rel'"
      by(blast dest: elim)
    
    from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<parallel> R'" by(rule Early_Semantics.Comm2)
    moreover from PRel R'Rel'T' have "(P' \<parallel> R', Q' \<parallel> S') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cClose1 Q' S' a x)
    have "x \<sharp> (P, R)" by fact
    hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+

    have "Q \<longmapsto> a<x> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: elim)
    
    have "S \<longmapsto> a<\<nu>x> \<prec> S'" by fact
    with RSimT xFreshR obtain R' where RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" and R'Rel'T': "(R', S') \<in> Rel'"
      by(blast dest: elim)
    
    from PTrans RTrans xFreshP have "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
      by(rule Early_Semantics.Close1)
    moreover from P'RelQ' R'Rel'T' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> S')) \<in> Rel''"
      by(blast intro: Par Res)
    ultimately show ?case by blast
  next
    case(cClose2 Q' S' a x)
    have "x \<sharp> (P, R)" by fact
    hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+

    have "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: elim)
    
    have "S \<longmapsto> a<x> \<prec> S'" by fact
    with RSimT obtain R' where RTrans: "R \<longmapsto>a<x> \<prec> R'" and R'Rel'T': "(R', S') \<in> Rel'" 
      by(blast dest: elim)
    
    from PTrans RTrans xFreshR have "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
      by(rule Early_Semantics.Close2)
    moreover from P'RelQ' R'Rel'T' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> S')) \<in> Rel''"
      by(blast intro: Par Res)
    ultimately show ?case by blast
  qed
qed

lemma parPres:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   a   :: name
  and   b   :: name
  and   Rel :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"
  
  assumes PSimQ:    "P \<leadsto>[Rel] Q"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     Par:      "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     Res:      "\<And>S T x. (S, T) \<in> Rel' \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel'"

  shows "P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
proof -
  note PSimQ 
  moreover have RSimR: "R \<leadsto>[Id] R" by(auto intro: reflexive)
  moreover note PRelQ moreover have "(R, R) \<in> Id" by auto
  moreover from Par have "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Id\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel'"
    by auto
  ultimately show ?thesis using Res by(rule parCompose)
qed

lemma resPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   x    :: name
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     ResSet: "\<And>(R::pi) (S::pi) (y::name). (R, S) \<in> Rel \<Longrightarrow> (<\<nu>y>R, <\<nu>y>S) \<in> Rel'"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel: "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "<\<nu>x>P \<leadsto>[Rel'] <\<nu>x>Q"
proof -
  from EqvtRel' show ?thesis
  proof(induct rule: simCasesCont[where C = "(P, x)"])
    case(Bound a y Q')
    have Trans: "<\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
    have "y \<sharp> (P, x)" by fact
    hence yineqx: "y \<noteq> x" and yFreshP: "y \<sharp> (P::pi)" by simp+
    from Trans yineqx show ?case
    proof(induct rule: resCasesB)
      case(Open Q')
      have QTrans: "Q \<longmapsto>(a::name)[x] \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<longmapsto> a[x] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
        by(blast dest: elim)

      have "<\<nu>x>P \<longmapsto>a<\<nu>y> \<prec> ([(y, x)] \<bullet> P')"
      proof -
        have aineqx: "a \<noteq> x" by fact
        with PTrans have "<\<nu>x>P \<longmapsto>a<\<nu>x> \<prec> P'" by(rule TransitionsEarly.Open)
        moreover have "a<\<nu>x> \<prec> P' = a<\<nu>y> \<prec> ([(y, x)] \<bullet> P')" 
        proof -
          from PTrans yFreshP have yFreshP': "y \<sharp> P'" by(force intro: freshTransition)
          thus ?thesis by(simp add: alphaBoundOutput name_swap)
        qed
        ultimately show ?thesis by simp
      qed
      moreover from EqvtRel P'RelQ' RelRel' have "([(y, x)] \<bullet> P', [(y, x)] \<bullet> Q') \<in> Rel'" 
        by(blast intro: eqvtRelI)
      ultimately show ?case by blast
    next
      case(Res Q')
      have QTrans: "Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact

      with PSimQ yFreshP obtain P' where PTrans: "P \<longmapsto>a<\<nu>y> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: elim)

      have xineqa: "x \<noteq> a" by fact
      with PTrans yineqx have ResTrans: "<\<nu>x>P \<longmapsto>a<\<nu>y> \<prec> (<\<nu>x>P')"
        by(blast intro: ResB)
      moreover from P'RelQ' have "((<\<nu>x>P'), (<\<nu>x>Q')) \<in> Rel'"
        by(rule ResSet)

      ultimately show "\<exists>P'. <\<nu>x>P \<longmapsto> a<\<nu>y> \<prec> P' \<and> (P', (<\<nu>x>Q')) \<in> Rel'" by blast
    qed
  next
    case(Free \<alpha> Q')
    have Trans: "<\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    have "\<exists>c::name. c \<sharp> (P, Q, Q', \<alpha>)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshAlpha: "c \<sharp> \<alpha>" and cFreshQ': "c \<sharp> Q'" and cFreshP: "c \<sharp> P"
      by(force simp add: fresh_prod)
    from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(simp add: alphaRes)
    moreover have "\<exists>P'.<\<nu>c>([(x, c)] \<bullet> P) \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
    proof -
      from Trans cFreshQ have "<\<nu>c>([(x, c)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> Q'" by(simp add: alphaRes)
      moreover from EqvtRel PSimQ have "([(x, c)] \<bullet> P) \<leadsto>[Rel] ([(x, c)] \<bullet> Q)"
        by(blast intro: eqvtI)
      ultimately show ?thesis using cFreshAlpha
        apply -
        apply(erule resCasesF)
        apply auto
        by(blast intro: ResF ResSet dest: elim)
    qed

    ultimately show "\<exists>P'.<\<nu>x>P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'" by auto
  qed
qed

lemma resChainI:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   lst :: "name list"

  assumes eqvtRel: "eqvt Rel"
  and     Res:     "\<And>R S x. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel"
  and     PRelQ:   "P \<leadsto>[Rel] Q"

  shows "(resChain lst) P \<leadsto>[Rel] (resChain lst) Q"
proof -
  show ?thesis
  proof(induct lst) (* Base case *)
    from PRelQ show "resChain [] P \<leadsto>[Rel] resChain [] Q" by simp
  next (* Inductive step *)
    fix a lst
    assume IH: "(resChain lst P) \<leadsto>[Rel] (resChain lst Q)"
    moreover from Res have "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel"
      by simp
    moreover have "Rel \<subseteq> Rel" by simp
    ultimately have "<\<nu>a>(resChain lst P) \<leadsto>[Rel] <\<nu>a>(resChain lst Q)" using eqvtRel
      by(rule_tac resPres)
    thus "resChain (a # lst) P \<leadsto>[Rel] resChain (a # lst) Q"
      by simp
  qed
qed

lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
 
  assumes PRelQ:    "(P, Q) \<in> Rel"
  and     Sim:      "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>[Rel] S"
  and     eqvtRel:  "eqvt Rel"

  shows "!P \<leadsto>[bangRel Rel] !Q"
proof -
  let ?Sim = "\<lambda>P Rs. (\<forall>a x Q'. Rs = a<\<nu>x> \<prec> Q' \<longrightarrow> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<longmapsto>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> bangRel Rel)) \<and>
                     (\<forall>\<alpha> Q'. Rs = \<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> bangRel Rel))"
  from eqvtRel have EqvtBangRel: "eqvt(bangRel Rel)" by(rule eqvtBangRel)

  {
    fix Pa Rs
    assume "!Q \<longmapsto> Rs" and "(Pa, !Q) \<in> bangRel Rel"
    hence "?Sim Pa Rs" using PRelQ
    proof(nominal_induct avoiding: Pa P rule: bangInduct)
      case(Par1B a x Q' Pa P)
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" by fact+
      thus "?Sim Pa (a<\<nu>x> \<prec> (Q' \<parallel> !Q))"
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        have PBRQ: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case 
        proof(auto simp add: residual.inject alpha')
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)

          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto> a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: elim)

          from PTrans xFreshR have "P \<parallel> R \<longmapsto> a<\<nu>x> \<prec> (P' \<parallel> R)"
            by(force intro: Early_Semantics.Par1B)
          moreover from P'RelQ' PBRQ have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto>a<\<nu>x> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> bangRel Rel" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R" and "y \<sharp> Q"
          from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q')"
            by(simp add: alphaBoundOutput)
          moreover from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          ultimately obtain P' where PTrans: "P \<longmapsto>a<\<nu>y> \<prec> P'" and P'RelQ': "(P', [(x, y)] \<bullet> Q') \<in> Rel"
            using \<open>y \<sharp> P\<close>
            by(blast dest: elim)
          from PTrans \<open>y \<sharp> R\<close> have "P \<parallel> R \<longmapsto>a<\<nu>y> \<prec> (P' \<parallel> R)" by(force intro: Early_Semantics.Par1B)
          moreover from P'RelQ' PBRQ have "(P' \<parallel> R, ([(x, y)] \<bullet> Q') \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
          with \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> have "(P' \<parallel> R, ([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) \<in> bangRel Rel"
            by(simp add: name_fresh_fresh name_swap)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto>a<\<nu>y> \<prec> P' \<and> (P', ([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) \<in> bangRel Rel"
            by blast
        qed
      qed
    next
      case(Par1F \<alpha> Q' Pa P)
      have QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and BR: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'" and RRel: "(P', Q') \<in> Rel"
            by(blast dest: elim)
          
          from PTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<parallel> R" by(rule TransitionsEarly.Par1F)
          moreover from RRel BR have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Par2B a x Q' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a<\<nu>x> \<prec> Q')" by simp
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" by fact+
      thus "?Sim Pa (a<\<nu>x> \<prec> (Q \<parallel> Q'))"
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+

        from EqvtBangRel show "?Sim (P \<parallel> R) (a<\<nu>x> \<prec> (Q \<parallel> Q'))"
        proof(auto simp add: residual.inject alpha')
          from RBRQ have "?Sim R (a<\<nu>x> \<prec> Q')" by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<longmapsto> a<\<nu>x> \<prec> R'" and R'BRQ': "(R', Q') \<in> (bangRel Rel)"
            by(metis elim)
          from RTrans xFreshP have "P \<parallel> R \<longmapsto> a<\<nu>x> \<prec> (P \<parallel> R')" by(auto intro: Early_Semantics.Par2B)
          moreover from PRelQ R'BRQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> (bangRel Rel)" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> a<\<nu>x> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> bangRel Rel" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q" and "y \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R"
          from RBRQ have "?Sim R (a<\<nu>x> \<prec> Q')" by(rule IH)
          with \<open>y \<sharp> Q'\<close> have "?Sim R (a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q'))" by(simp add: alphaBoundOutput)
          with \<open>y \<sharp> R\<close> obtain R' where RTrans: "R \<longmapsto> a<\<nu>y> \<prec> R'" and R'BRQ': "(R', ([(x, y)] \<bullet> Q')) \<in> (bangRel Rel)"
            by(metis elim)
          from RTrans \<open>y \<sharp> P\<close> have "P \<parallel> R \<longmapsto> a<\<nu>y> \<prec> (P \<parallel> R')" by(auto intro: Early_Semantics.Par2B)
          moreover from PRelQ R'BRQ' have "(P \<parallel> R', Q \<parallel> ([(x, y)] \<bullet> Q')) \<in> (bangRel Rel)" by(rule Rel.BRPar)
          with \<open>y \<sharp> Q\<close> \<open>x \<sharp> Q\<close> have "(P \<parallel> R', ([(y, x)] \<bullet> Q) \<parallel> ([(y, x)] \<bullet> Q')) \<in> (bangRel Rel)"
            by(simp add: name_swap name_fresh_fresh)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> a<\<nu>y> \<prec> P' \<and> (P', ([(y, x)] \<bullet> Q) \<parallel> ([(y, x)] \<bullet> Q')) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Par2F \<alpha> Q' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (\<alpha> \<prec> Q')" by simp
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from RBRQ IH have "\<exists>R'. R \<longmapsto> \<alpha> \<prec> R' \<and> (R', Q') \<in> bangRel Rel"
            by(metis elim)
          then obtain R' where RTrans: "R \<longmapsto> \<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> bangRel Rel"
            by blast

          from RTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P \<parallel> R'" by(rule TransitionsEarly.Par2F)
          moreover from PRelQ R'RelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show " \<exists>P'. P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Comm1 a Q' b Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a[b] \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto>a<b> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<longmapsto> a<b> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: elim)
          
          from IH RBRQ have RTrans: "\<exists>R'. R \<longmapsto> a[b] \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
            by(metis elim)
          then obtain R' where RTrans: "R \<longmapsto> a[b] \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
            by blast
          
          from PTrans RTrans have "P \<parallel> R \<longmapsto>\<tau> \<prec> P' \<parallel> R'" by(rule TransitionsEarly.Comm1)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', Q' \<parallel> Q'') \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Comm2 a b Q' Q'')
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a<b> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a[b] \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<longmapsto> a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: elim)

          from IH RBRQ have RTrans: "\<exists>R'. R \<longmapsto> a<b> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
            by(metis elim)
          then obtain R' where RTrans: "R \<longmapsto> a<b> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
            by blast

          from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<parallel> R'" by(rule TransitionsEarly.Comm2)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', Q' \<parallel> Q'') \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Close1 a x Q' Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<longrightarrow> ?Sim Pa (a<\<nu>x> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have xFreshQ: "x \<sharp> Q" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      moreover have xFreshPa: "x \<sharp> Pa" by fact
      ultimately show ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
             by(blast dest: elim)

           from RBRQ xFreshR IH have "\<exists>R'. R \<longmapsto>a<\<nu>x> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
             by(metis elim)
           then obtain R' where RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
             by blast

           from PTrans RTrans xFreshP have "P \<parallel> R \<longmapsto>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
             by(rule Early_Semantics.Close1)     
           moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel"
             by(force intro: Rel.BRPar BRRes)
           ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel" by blast
         qed
      qed
    next
      case(Close2 a x Q' Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a<x> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      have xFreshQ: "x \<sharp> Q" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: elim)

          from RBRQ IH have "\<exists>R'.  R \<longmapsto>a<x> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
            by auto
          then obtain R' where RTrans: "R \<longmapsto> a<x> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
            by blast

          from PTrans RTrans xFreshR have "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Early_Semantics.Close2)      
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel"
            by(force intro: Rel.BRPar BRRes)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(Bang Rs Pa P)
      hence IH: "\<And>Pa. (Pa, Q \<parallel> !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa Rs" by simp
      have "(Pa, !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        hence "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
        with PRelQ have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule BRPar)
        with IH have "?Sim (P \<parallel> !P) Rs" by simp
        thus ?case by(force intro: TransitionsEarly.Bang)
      qed
    qed
  }

  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?thesis by(auto simp add: strongSimEarly_def)
qed

end
