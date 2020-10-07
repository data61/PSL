(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Sim_Pres
  imports Weak_Early_Sim
begin

lemma tauPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "\<tau>.(P) \<leadsto><Rel> \<tau>.(Q)"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "\<tau>.(Q) \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  hence False by(induct rule: tauCases', auto)
  thus ?case by simp
next
  case(Free Q' \<alpha>)
  have "\<tau>.(Q) \<longmapsto>(\<alpha> \<prec> Q')" by fact
  thus ?case
  proof(induct rule: tauCases', auto simp only: pi.inject residual.inject)
    have "\<tau>.(P) \<Longrightarrow>\<^sup>^ \<tau> \<prec> P" by(rule Tau)
    with PRelQ show "\<exists>P'. \<tau>.(P) \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<and> (P', Q) \<in> Rel" by blast
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

  shows "a<x>.P \<leadsto><Rel> a<x>.Q"
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
    have "a<x>.P \<Longrightarrow>\<^sup>^(a<u>) \<prec> P[x::=u]"
      by(rule Input)
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

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "a{b}.P \<leadsto><Rel> a{b}.Q"
proof(induct rule: simCases)
  case(Bound Q' c x)
  have "a{b}.Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
  hence False by(induct rule: outputCases', auto)
  thus ?case by simp
next
  case(Free Q' \<alpha>)
  have "a{b}.Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus "\<exists>P'. a{b}.P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: outputCases', auto simp add: pi.inject residual.inject)
    have "a{b}.P \<Longrightarrow>\<^sup>^ a[b] \<prec> P" by(rule Output)
    with PRelQ show "\<exists>P'. a{b}.P \<Longrightarrow>\<^sup>^ a[b] \<prec> P' \<and> (P', Q) \<in> Rel" by blast
  qed
qed

lemma matchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto><Rel> Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     RelStay: "\<And>R S c. (R, S) \<in> Rel \<Longrightarrow> ([c\<frown>c]R, S) \<in> Rel"

  shows "[a\<frown>b]P \<leadsto><Rel'> [a\<frown>b]Q"
proof(induct rule: simCases)
  case(Bound Q' c x)
  have "x \<sharp> [a\<frown>b]P" by fact
  hence xFreshP: "(x::name) \<sharp> P" by simp
  have "[a\<frown>b]Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case Match
    have "Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P' where PTrans: "P \<Longrightarrow>c<\<nu>x> \<prec> P'"
                                   and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have "[a\<frown>a]P \<Longrightarrow>c<\<nu>x> \<prec> P'" by(rule Weak_Early_Step_Semantics.Match)
    moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
next
  case(Free Q' \<alpha>)
  have "[a\<frown>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case Match
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
      by(blast dest: simE)
    thus ?case
    proof(induct rule: transitionCases)
      case Step
      have "P \<Longrightarrow>\<alpha> \<prec> P'" by fact
      hence "[a\<frown>a]P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Match)
      with RelRel' \<open>(P', Q') \<in> Rel\<close> show ?case by(force simp add: weakFreeTransition_def)
    next
      case Stay
      have "[a\<frown>a]P \<Longrightarrow>\<^sup>^\<tau> \<prec> [a\<frown>a]P" by(simp add: weakFreeTransition_def)
      moreover from \<open>(P, Q') \<in> Rel\<close> have "([a\<frown>a]P, Q') \<in> Rel" by(blast intro: RelStay)
      ultimately show ?case using RelRel' by blast
    qed
  qed
qed

lemma mismatchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto><Rel> Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     RelStay: "\<And>R S c d. \<lbrakk>(R, S) \<in> Rel; c \<noteq> d\<rbrakk> \<Longrightarrow> ([c\<noteq>d]R, S) \<in> Rel"

  shows "[a\<noteq>b]P \<leadsto><Rel'> [a\<noteq>b]Q"
proof(induct rule: simCases)
  case(Bound Q' c x)
  have "x \<sharp> [a\<noteq>b]P" by fact
  hence xFreshP: "(x::name) \<sharp> P" by simp
  have "[a\<noteq>b]Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: mismatchCases)
    case Mismatch
    have aineqb: "a \<noteq> b" by fact
    have "Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P' where PTrans: "P \<Longrightarrow>c<\<nu>x> \<prec> P'"
                                   and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans aineqb have "[a\<noteq>b]P \<Longrightarrow>c<\<nu>x> \<prec> P'" by(rule Weak_Early_Step_Semantics.Mismatch)
    moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
next
  case(Free Q' \<alpha>)
  have "[a\<noteq>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: mismatchCases)
    case Mismatch
    have aineqb: "a \<noteq> b" by fact
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
      by(blast dest: simE)
    thus ?case
    proof(induct rule: transitionCases)
      case Step
      have "P \<Longrightarrow>\<alpha> \<prec> P'" by fact
      hence "[a\<noteq>b]P \<Longrightarrow>\<alpha> \<prec> P'" using aineqb by(rule Weak_Early_Step_Semantics.Mismatch)
      with RelRel' \<open>(P', Q') \<in> Rel\<close> show ?case by(force simp add: weakFreeTransition_def)
    next
      case Stay
      have "[a\<noteq>b]P \<Longrightarrow>\<^sup>^\<tau> \<prec> [a\<noteq>b]P" by(simp add: weakFreeTransition_def)
      moreover from \<open>(P, Q') \<in> Rel\<close> aineqb have "([a\<noteq>b]P, Q') \<in> Rel" by(blast intro: RelStay)
      ultimately show ?case using RelRel' by blast
    qed
  qed
qed

lemma parCompose:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   S     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"
  
  assumes PSimQ:    "P \<leadsto><Rel> Q"
  and     RSimT:    "R \<leadsto><Rel'> S"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     RRel'T:   "(R, S) \<in> Rel'"
  and     Par:      "\<And>P' Q' R' S'. \<lbrakk>(P', Q') \<in> Rel; (R', S') \<in> Rel'\<rbrakk> \<Longrightarrow> (P' \<parallel> R', Q' \<parallel> S') \<in> Rel''"
  and     Res:      "\<And>T U x. (T, U) \<in> Rel'' \<Longrightarrow> (<\<nu>x>T, <\<nu>x>U) \<in> Rel''"

  shows "P \<parallel> R \<leadsto><Rel''> Q \<parallel> S"
proof -
  show ?thesis
  proof(induct rule: simCases)
    case(Bound Q' a x)
    have "x \<sharp> P \<parallel> R" by fact
    hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
    have "Q \<parallel> S \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" and xFreshT: "x \<sharp> S" by fact+
      from xFreshP PSimQ QTrans obtain P' where PTrans:"P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P' \<parallel> R)" by(rule Weak_Early_Step_Semantics.Par1B)
      moreover from P'RelQ' RRel'T have "(P' \<parallel> R, Q' \<parallel> S) \<in> Rel''" by(rule Par)
      ultimately show ?case by blast
    next
      case(cPar2 S')
      have STrans: "S \<longmapsto> a<\<nu>x> \<prec> S'" and xFreshQ: "x \<sharp> Q" by fact+
      from xFreshR RSimT STrans obtain R' where RTrans:"R \<Longrightarrow>a<\<nu>x> \<prec> R'"
                                            and R'Rel'T': "(R', S') \<in>  Rel'"
        by(blast dest: simE)
      from RTrans xFreshP xFreshR have ParTrans: "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> R')"
        by(blast intro: Weak_Early_Step_Semantics.Par2B)
      moreover from PRelQ R'Rel'T' have "(P \<parallel> R', Q \<parallel>  S') \<in> Rel''" by(rule Par)
      ultimately show ?case by blast
    qed
  next
    case(Free QT' \<alpha>)
    have "Q \<parallel> S \<longmapsto> \<alpha> \<prec> QT'" by fact
    thus ?case
    proof(induct rule: parCasesF[of _ _ _ _ _ "(P, R)"])
      case(cPar1 Q')
      have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans have Trans: "P \<parallel> R \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<parallel> R" by(rule Weak_Early_Semantics.Par1F)
      moreover from PRel RRel'T have "(P' \<parallel> R, Q' \<parallel> S) \<in> Rel''" by(blast intro: Par)
      ultimately show ?case by blast
    next
      case(cPar2 S')
      have "S \<longmapsto> \<alpha> \<prec> S'" by fact
      with RSimT obtain R' where RTrans: "R \<Longrightarrow>\<^sup>^ \<alpha> \<prec> R'" and RRel: "(R', S') \<in> Rel'"
        by(blast dest: simE)
      from RTrans have Trans: "P \<parallel> R \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P \<parallel> R'" by(rule Weak_Early_Semantics.Par2F)
      moreover from PRelQ RRel have "(P \<parallel> R', Q \<parallel> S') \<in> Rel''" by(blast intro: Par)
      ultimately show ?case by blast
    next
      case(cComm1 Q' S' a b)
      have QTrans: "Q \<longmapsto> a<b> \<prec> Q'" and STrans: "S \<longmapsto> a[b] \<prec> S'" by fact+

      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a<b> \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      
      from RSimT STrans obtain R' where RTrans: "R \<Longrightarrow>a[b] \<prec> R'"
                                    and RRel: "(R', S') \<in> Rel'"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      
      from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm1)
      hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'" 
        by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)

      moreover from P'RelQ' RRel have "(P' \<parallel> R', Q' \<parallel> S') \<in> Rel''" by(rule Par)
      ultimately show ?case by blast
    next
      case(cComm2 Q' S' a b)
      have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" and STrans: "S \<longmapsto>a<b> \<prec> S'" by fact+
      
      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a[b] \<prec> P'"
                                    and PRel: "(P', Q') \<in> Rel"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      
      from RSimT STrans obtain R' where RTrans: "R \<Longrightarrow>a<b> \<prec> R'"
                                   and R'Rel'T': "(R', S') \<in> Rel'"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      
      from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm2)
      hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> R'" 
        by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)
      moreover from PRel R'Rel'T' have "(P' \<parallel> R', Q' \<parallel> S') \<in> Rel''" by(rule Par)
      ultimately show ?case by blast
    next
      case(cClose1 Q' S' a x)
      have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" and STrans: "S \<longmapsto>a<\<nu>x> \<prec> S'" by fact+
      have "x \<sharp> (P, R)" by fact
      hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by(simp add: fresh_prod)+
      
      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a<x> \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      
      from RSimT STrans xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'" 
                                            and R'Rel'T': "(R', S') \<in> Rel'"
        by(blast dest: simE)
       
      from PTrans RTrans xFreshP have Trans: "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
        by(rule Weak_Early_Step_Semantics.Close1)
      hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> <\<nu>x>(P' \<parallel> R')" 
        by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)
      moreover from P'RelQ' R'Rel'T' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> S')) \<in> Rel''"
        by(blast intro: Par Res)
      ultimately show ?case by blast
    next
      case(cClose2 Q' S' a x)
      have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and STrans: "S \<longmapsto>a<x> \<prec> S'" by fact+
      have "x \<sharp> (P, R)" by fact
      hence xFreshR: "x \<sharp> R" and xFreshP: "x \<sharp> P" by(simp add: fresh_prod)+

      from PSimQ QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      from RSimT STrans obtain R' where RTrans: "R \<Longrightarrow>a<x> \<prec> R'"
                                    and R'Rel'T': "(R', S') \<in> Rel'"
        by(fastforce dest: simE simp add: weakFreeTransition_def)
      from PTrans RTrans xFreshR have Trans: "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
        by(rule Weak_Early_Step_Semantics.Close2)
      hence "P \<parallel> R \<Longrightarrow>\<^sup>^\<tau> \<prec> <\<nu>x>(P' \<parallel> R')" 
        by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)
      moreover from P'RelQ' R'Rel'T' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> S')) \<in> Rel''"
        by(blast intro: Par Res)
      ultimately show ?case by blast
    qed
  qed
qed

lemma parPres:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   a   :: name
  and   Rel :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"
  
  assumes PSimQ:    "P \<leadsto><Rel> Q"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     Par:      "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     Res:      "\<And>S T x. (S, T) \<in> Rel' \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel'"

  shows "P \<parallel> R \<leadsto><Rel'> Q \<parallel> R"
proof -
  note PSimQ 
  moreover have RSimR: "R \<leadsto><Id> R" by(auto intro: reflexive)
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

  assumes PSimQ: "P \<leadsto><Rel> Q"
  and     ResRel: "\<And>R S y. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>y>R, <\<nu>y>S) \<in> Rel'"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel: "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "<\<nu>x>P \<leadsto><Rel'> <\<nu>x>Q"
proof -
  from EqvtRel' show ?thesis
  proof(induct rule: simCasesCont[where C="(P, x)"])
    case(Bound a y Q')
    have Trans: "<\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
    have "y \<sharp> (P, x)" by fact
    hence yineqx: "y \<noteq> x" and yFreshP: "y \<sharp> P" by(simp add: fresh_prod)+
    from Trans yineqx show ?case
    proof(induct rule: resCasesB)
      case(Open Q')
      have QTrans: "Q \<longmapsto>a[x] \<prec> Q'" and aineqx: "a \<noteq> x" by fact+

      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^a[x] \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      from PTrans aineqx have "<\<nu>x>P \<Longrightarrow>a<\<nu>x> \<prec> P'" 
        by(force intro: Weak_Early_Step_Semantics.Open simp add: weakFreeTransition_def)
      with \<open>y \<sharp> P\<close> \<open>y \<noteq> x\<close> have "<\<nu>x>P \<Longrightarrow>a<\<nu>y> \<prec> ([(y, x)] \<bullet> P')"
        by(force intro: weakTransitionAlpha simp add: abs_fresh name_swap)
      moreover from EqvtRel P'RelQ' RelRel' have "([(y, x)] \<bullet> P', [(y, x)] \<bullet> Q') \<in> Rel'"
        by(blast intro: eqvtRelI)
      ultimately show ?case by blast
    next
      case(Res Q')
      have QTrans: "Q \<longmapsto>a<\<nu>y> \<prec> Q'" and xineqa: "x \<noteq> a" by fact+

      from PSimQ yFreshP QTrans obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>y> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans xineqa yineqx yFreshP have ResTrans: "<\<nu>x>P \<Longrightarrow>a<\<nu>y> \<prec> (<\<nu>x>P')"
        by(blast intro: Weak_Early_Step_Semantics.ResB)
      moreover from P'RelQ' have "((<\<nu>x>P'), (<\<nu>x>Q')) \<in> Rel'"
        by(rule ResRel)
      ultimately show ?case by blast
    qed
  next
    case(Free \<alpha> Q')
    have QTrans: "<\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    have "\<exists>c::name. c \<sharp> (P, Q, Q', \<alpha>)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshAlpha: "c \<sharp> \<alpha>" and cFreshQ': "c \<sharp> Q'" and cFreshP: "c \<sharp> P"
      by(force simp add: fresh_prod)
    from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(simp add: alphaRes)
    moreover have "\<exists>P'.<\<nu>c>([(x, c)] \<bullet> P) \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
    proof -
      from QTrans cFreshQ have "<\<nu>c>([(x, c)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> Q'" by(simp add: alphaRes)
      moreover have "c \<sharp> \<alpha>" by(rule cFreshAlpha)
      moreover from PSimQ EqvtRel have "([(x, c)] \<bullet> P) \<leadsto><Rel> ([(x, c)] \<bullet> Q)"
        by(blast intro: eqvtI)
      ultimately show ?thesis
        apply(induct rule: resCasesF, auto simp add: residual.inject pi.inject name_abs_eq)
        by(blast intro: ResF ResRel dest: simE)
    qed

    ultimately show ?case by force
  qed
qed

lemma resChainI:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   lst :: "name list"

  assumes eqvtRel: "eqvt Rel"
  and     Res:     "\<And>R S y. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>y>R, <\<nu>y>S) \<in> Rel"
  and     PRelQ:   "P \<leadsto><Rel> Q"

  shows "(resChain lst) P \<leadsto><Rel> (resChain lst) Q"
proof -
  show ?thesis
  proof(induct lst) (* Base case *)
    from PRelQ show "resChain [] P \<leadsto><Rel> resChain [] Q" by simp
  next (* Inductive step *)
    fix a lst
    assume IH: "(resChain lst P) \<leadsto><Rel> (resChain lst Q)"
    moreover from Res have "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel"
      by simp
    moreover have "Rel \<subseteq> Rel" by simp
    ultimately have "<\<nu>a>(resChain lst P) \<leadsto><Rel> <\<nu>a>(resChain lst Q)" using eqvtRel
      by(rule_tac resPres)
    thus "resChain (a # lst) P \<leadsto><Rel> resChain (a # lst) Q"
      by simp
  qed
qed

lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
 
  assumes PRelQ:       "(P, Q) \<in> Rel"
  and     Sim:         "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel> S"

  and     ParComp:     "\<And>R S T U. \<lbrakk>(R, S) \<in> Rel; (T, U) \<in> Rel'\<rbrakk> \<Longrightarrow> (R \<parallel> T, S \<parallel> U) \<in> Rel'"
  and     Res:         "\<And>R S x. (R, S) \<in> Rel' \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel'"

  and     RelStay:        "\<And>R S. (R \<parallel> !R, S) \<in> Rel' \<Longrightarrow> (!R, S) \<in> Rel'"
  and     BangRelRel': "(bangRel Rel) \<subseteq> Rel'"
  and     eqvtRel':    "eqvt Rel'"

  shows "!P \<leadsto><Rel'> !Q"
proof -
  let ?Sim = "\<lambda>P Rs. (\<forall>a x Q'. Rs = a<\<nu>x> \<prec> Q' \<longrightarrow> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel')) \<and>
                     (\<forall>\<alpha> Q'. Rs = \<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'))"
  {
    fix Rs P
    assume "!Q \<longmapsto> Rs" and "(P, !Q) \<in> bangRel Rel"
    hence "?Sim P Rs" using PRelQ
    proof(nominal_induct avoiding: P rule: bangInduct)
      case(Par1B a x Q')
      have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and xFreshQ: "x \<sharp> Q" by fact+
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelT: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        from PRelQ have PSimQ: "P \<leadsto><Rel> Q" by(rule Sim)
        from \<open>x \<sharp> P\<close> \<open>x \<sharp> Q\<close> show ?case
        proof(auto simp add: residual.inject alpha' name_fresh_fresh)
          from PSimQ QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                                and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)
          from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>a<\<nu>x>\<prec> (P' \<parallel> R)"
            by(rule Weak_Early_Step_Semantics.Par1B)
          moreover from P'RelQ' RBangRelT BangRelRel' have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> Rel'"
            by(blast intro: Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> Rel'" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R"
          from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q')" by(simp add: alphaBoundOutput)
          with PSimQ \<open>y \<sharp> P\<close> obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>y> \<prec> P'"
                                         and P'RelQ': "(P', [(x, y)] \<bullet> Q') \<in> Rel"
            by(blast dest: simE)
          from PTrans \<open>y \<sharp> R\<close> have "P \<parallel> R \<Longrightarrow>a<\<nu>y>\<prec> (P' \<parallel> R)" by(rule Weak_Early_Step_Semantics.Par1B)
          moreover from P'RelQ' RBangRelT BangRelRel' have "(P' \<parallel> R, ([(y, x)] \<bullet> Q') \<parallel> !Q) \<in> Rel'"
            by(fastforce intro: Rel.BRPar simp add: name_swap) 
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> P' \<and> (P', ([(y, x)] \<bullet> Q') \<parallel> !Q) \<in> Rel'" by blast
        qed
      qed
    next
      case(Par1F \<alpha> Q' P)
      have QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto><Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from PTrans have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule Weak_Early_Semantics.Par1F)
          moreover from P'RelQ' RBangRelQ have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel"
            by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> Rel'" using BangRelRel' by blast
        qed
      qed
    next
      case(Par2B a x Q' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (a<\<nu>x> \<prec> Q')" by simp
      have xFreshQ: "x \<sharp> Q" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case using \<open>x \<sharp> Q\<close>
        proof(auto simp add: residual.inject alpha' name_fresh_fresh)
          from IH RBangRelQ have "?Sim R (a<\<nu>x> \<prec> Q')" by blast
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'" and R'BangRelQ': "(R', Q') \<in> Rel'"
            by(blast dest: simE)
          from RTrans xFreshP have "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> R')"
            by(auto intro: Weak_Early_Step_Semantics.Par2B)
          moreover from PRelQ R'BangRelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'"
            by(rule ParComp)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> Rel'" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q'" and "y \<sharp> R" and "y \<sharp> P"
          from IH RBangRelQ have "?Sim R (a<\<nu>x> \<prec> Q')" by blast
          with \<open>y \<sharp> Q'\<close> have  "?Sim R (a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q'))" by(simp add: alphaBoundOutput)
          with \<open>y \<sharp> R\<close>obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>y> \<prec> R'" and R'BangRelQ': "(R', [(x, y)] \<bullet> Q') \<in> Rel'"
            by(blast dest: simE)
          from RTrans \<open>y \<sharp> P\<close> have "P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> (P \<parallel> R')"
            by(auto intro: Weak_Early_Step_Semantics.Par2B)
          moreover from PRelQ R'BangRelQ' have "(P \<parallel> R', Q \<parallel> ([(y, x)] \<bullet> Q')) \<in> Rel'"
            by(fastforce intro: ParComp simp add: name_swap)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> P' \<and> (P', Q \<parallel> ([(y, x)] \<bullet> Q')) \<in> Rel'" by blast
        qed
      qed
    next
      case(Par2F \<alpha> Q' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (\<alpha> \<prec> Q')" by simp
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from RBangRelQ have "?Sim R (\<alpha> \<prec> Q')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>\<^sup>^\<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> Rel'"
            by(blast dest: simE)
          from RTrans have "P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule Weak_Early_Semantics.Par2F)
          moreover from PRelQ R'RelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'" by(rule ParComp)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> Rel'" by blast
        qed
      qed
    next
      case(Comm1 a Q' b Q'' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (a[b] \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<b> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto><Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a<b> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(fastforce dest: simE simp add: weakFreeTransition_def)

          from RBangRelQ have "?Sim R (a[b] \<prec> Q'')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>a[b] \<prec> R'"
                           and R'RelQ'': "(R', Q'') \<in> Rel'"
            by(fastforce dest: simE simp add: weakFreeTransition_def)
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Comm1)
          hence "P \<parallel> R \<Longrightarrow>\<^sub>\<tau> P' \<parallel> R'" 
            by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> Rel'"
            by(rule ParComp)
          ultimately show "\<exists>P'. (P \<parallel> R, P') \<in> {(P, P'). P \<longmapsto> \<tau> \<prec> P'}\<^sup>* \<and> (P', Q' \<parallel> Q'') \<in> Rel'"
            by auto
        qed
      qed
    next
      case(Comm2 a b Q' Q'' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (a<b> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto><Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(fastforce dest: simE simp add: weakFreeTransition_def)

          from RBangRelQ have "?Sim R (a<b> \<prec> Q'')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>a<b> \<prec> R'" and R'BangRelQ'': "(R', Q'') \<in> Rel'"
            by(fastforce dest: simE simp add: weakFreeTransition_def)
        
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Comm2)
          hence "P \<parallel> R \<Longrightarrow>\<^sub>\<tau> P' \<parallel> R'" 
            by(auto simp add: trancl_into_rtrancl dest: Weak_Early_Step_Semantics.tauTransitionChain)
          moreover from P'RelQ' R'BangRelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> Rel'"
            by(rule ParComp)
          ultimately show "\<exists>P'. (P \<parallel> R, P') \<in> {(P, P'). P \<longmapsto> \<tau> \<prec> P'}\<^sup>* \<and> (P', Q' \<parallel> Q'') \<in> Rel'" by auto
        qed
      qed
    next
      case(Close1 a x Q' Q'' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (a<\<nu>x> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshR: "x \<sharp> R" and xFreshP: "x \<sharp> P" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto><Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a<x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(fastforce dest: simE simp add: weakFreeTransition_def)
          
          from RBangRelQ have "?Sim R (a<\<nu>x> \<prec> Q'') " by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'"
                                   and R'RelQ'': "(R', Q'') \<in> Rel'"
            by(blast dest: simE)
        
          from PTrans RTrans xFreshP have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Close1)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> Rel'"
            by(force intro: ParComp Res)
          ultimately show "\<exists>P'. (P \<parallel> R, P') \<in> {(P, P'). P \<longmapsto> \<tau> \<prec> P'}\<^sup>* \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> Rel'" by auto
        qed
      qed
    next
      case(Close2 a x Q' Q'' P)
      hence IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P (a<x> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto><Rel> Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                          and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from RBangRelQ have "?Sim R (a<x> \<prec> Q'')" by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<x> \<prec> R'"
                                       and R'RelQ'': "(R', Q'') \<in> Rel'"
            by(fastforce simp add: weakFreeTransition_def)
          from PTrans RTrans xFreshR have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Close2)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> Rel'"
            by(force intro: ParComp Res)
          ultimately show "\<exists>P'. (P \<parallel> R, P') \<in> {(P, P'). P \<longmapsto> \<tau> \<prec> P'}\<^sup>* \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> Rel'" by auto
        qed
      qed
    next
      case(Bang Rs)
      hence IH: "\<And>P. (P, Q \<parallel> !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim P Rs" by simp
      have "(P, !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        hence "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
        with PRelQ have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
        hence IH: "?Sim (P \<parallel> !P) Rs" by(rule IH)
        show ?case
        proof(intro conjI allI impI)
          fix Q' a x
          assume "Rs = a<\<nu>x> \<prec> Q'" and "x \<sharp> !P"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>a<\<nu>x> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> Rel'" using IH
            by(auto simp add: residual.inject)
          from PTrans have "!P \<Longrightarrow>a<\<nu>x> \<prec> P'"
            by(force intro: Weak_Early_Step_Semantics.Bang simp add: weakFreeTransition_def)
          with P'RelQ' show "\<exists>P'. !P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel'" by blast
        next
          fix Q' \<alpha>
          assume "Rs = \<alpha> \<prec> Q'"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> Rel'" using IH
            by auto
          from PTrans show "\<exists>P'. !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'" using P'RelQ'
          proof(induct rule: transitionCases)
            case Step
            have "P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'" by fact
            hence "!P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Bang)
            with P'RelQ' show ?case by(force simp add: weakFreeTransition_def)
          next
            case Stay
            have "!P \<Longrightarrow>\<^sup>^\<tau> \<prec> !P" by(simp add: weakFreeTransition_def)
            moreover assume "(P \<parallel> !P, Q') \<in> Rel'"
            hence "(!P, Q') \<in> Rel'" by(blast intro: RelStay)
            ultimately show ?case by blast
          qed
        qed
      qed
    qed
  }
  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
  ultimately show ?thesis by(auto simp add: weakSimulation_def)
qed

lemma bangRelSim:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel'l :: "(pi \<times> pi) set"

  assumes PBangRelQ: "(P, Q) \<in> bangRel Rel"
  and     Sim:       "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel> S"

  and     ParComp:     "\<And>R S T U. \<lbrakk>(R, S) \<in> Rel; (T, U) \<in> Rel'\<rbrakk> \<Longrightarrow> (R \<parallel> T, S \<parallel> U) \<in> Rel'"
  and     Res:         "\<And>R S x. (R, S) \<in> Rel' \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel'"

  and     RelStay:        "\<And>R S. (R \<parallel> !R, S) \<in> Rel' \<Longrightarrow> (!R, S) \<in> Rel'"
  and     BangRelRel': "(bangRel Rel) \<subseteq> Rel'"
  and     eqvtRel':    "eqvt Rel'"
  and     Eqvt: "eqvt Rel"

  shows "P \<leadsto><Rel'> Q"
proof -
  from PBangRelQ show ?thesis
  proof(induct rule: bangRel.induct)
    case(BRBang P Q)
    have PRelQ: "(P, Q) \<in> Rel" by fact
    thus ?case using ParComp Res BangRelRel' eqvtRel' Eqvt RelStay Sim
      by(rule_tac bangPres)
  next
    case(BRPar P Q R T) 
    have "(P, Q) \<in> Rel" by fact
    moreover hence "P \<leadsto><Rel> Q" by(rule Sim)
    moreover have "R \<leadsto><Rel'> T" by fact
    moreover have "(R, T) \<in> bangRel Rel" by fact
    ultimately show ?case using ParComp eqvtRel' Res Eqvt BangRelRel'
      by(blast intro: parCompose)
  next
    case(BRRes P Q x)
    have "P \<leadsto><Rel'> Q" by fact
    thus ?case using BangRelRel' eqvtRel' Res by(blast intro: resPres)
  qed
qed

end
