(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Step_Sim_Pres
  imports Weak_Early_Step_Sim
begin

lemma tauPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "\<tau>.(P) \<leadsto>\<guillemotleft>Rel\<guillemotright> \<tau>.(Q)"
proof(induct rule: simCases)
  case(Bound a x Q')
  have "\<tau>.(Q) \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  hence False by(induct rule: tauCases', auto)
  thus ?case by simp
next
  case(Free \<alpha> Q')
  have "\<tau>.(Q) \<longmapsto>(\<alpha> \<prec> Q')" by fact
  thus ?case
  proof(induct rule: tauCases', auto simp add: pi.inject residual.inject)
    have "\<tau>.(P) \<Longrightarrow> \<tau> \<prec> P" by(rule Weak_Early_Step_Semantics.Tau)
    with PRelQ show "\<exists>P'. \<tau>.(P) \<Longrightarrow> \<tau> \<prec> P' \<and> (P', Q) \<in> Rel" by blast
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

  shows "a<x>.P \<leadsto>\<guillemotleft>Rel\<guillemotright> a<x>.Q"
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
    have "a<x>.P \<Longrightarrow>(a<u>) \<prec> (P[x::=u])"
      by(rule Weak_Early_Step_Semantics.Input)
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

  shows "a{b}.P \<leadsto>\<guillemotleft>Rel\<guillemotright> a{b}.Q"
proof(induct rule: simCases)
  case(Bound c x Q')
  have "a{b}.Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
  hence False by(induct rule: outputCases', auto)
  thus ?case by simp
next
  case(Free \<alpha> Q')
  have "a{b}.Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus "\<exists>P'. a{b}.P \<Longrightarrow> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: outputCases', auto simp add: pi.inject residual.inject)
    have "a{b}.P \<Longrightarrow> a[b] \<prec> P" by(rule Weak_Early_Step_Semantics.Output)
    with PRelQ show "\<exists>P'. a{b}.P \<Longrightarrow> a[b] \<prec> P' \<and> (P', Q) \<in> Rel" by blast
  qed
qed

lemma matchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     RelRel': "Rel \<subseteq> Rel'"

  shows "[a\<frown>b]P \<leadsto>\<guillemotleft>Rel'\<guillemotright> [a\<frown>b]Q"
proof(induct rule: simCases)
  case(Bound c x Q')
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
  case(Free \<alpha> Q')
  have "[a\<frown>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case Match
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have "[a\<frown>a]P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Match)
    with RelRel' PRel show ?case by blast
  qed
qed

lemma mismatchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     RelRel': "Rel \<subseteq> Rel'"

  shows "[a\<noteq>b]P \<leadsto>\<guillemotleft>Rel'\<guillemotright> [a\<noteq>b]Q"
proof(induct rule: simCases)
  case(Bound c x Q')
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
  case(Free \<alpha> Q')
  have "[a\<noteq>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: mismatchCases)
    case Mismatch
    have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Mismatch)
    with RelRel' PRel show ?case by blast
  qed
qed

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     C: "Id \<subseteq> Rel'"

  shows "P \<oplus> R \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q \<oplus> R"
proof(induct rule: simCases)
  case(Bound a x Q')
  have "x \<sharp> P \<oplus> R" by fact
  hence xFreshP: "(x::name) \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
  have "Q \<oplus> R \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: sumCases)
    case Sum1
    have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
    with xFreshP PSimQ obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have "P \<oplus> R \<Longrightarrow>a<\<nu>x> \<prec> P'" by(rule Weak_Early_Step_Semantics.Sum1)
    moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  next
    case Sum2
    from \<open>R \<longmapsto>a<\<nu>x> \<prec> Q'\<close> have "P \<oplus> R \<longmapsto>a<\<nu>x> \<prec> Q'" by(rule Early_Semantics.Sum2)
    hence "P \<oplus> R \<Longrightarrow>a<\<nu>x> \<prec> Q'" by(rule Weak_Early_Step_Semantics.singleActionChain)
    moreover from C have "(Q', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> Q')
  have "Q \<oplus> R \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: sumCases)
    case Sum1
    have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel" 
      by(blast dest: simE)
    from PTrans have "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Sum1)
    with RelRel' PRel show ?case by blast
  next
    case Sum2
    from \<open>R \<longmapsto>\<alpha> \<prec> Q'\<close> have "P \<oplus> R \<longmapsto>\<alpha> \<prec> Q'" by(rule Early_Semantics.Sum2)
    hence "P \<oplus> R \<Longrightarrow>\<alpha> \<prec> Q'" by(rule Weak_Early_Step_Semantics.singleActionChain)
    moreover from C have "(Q', Q') \<in> Rel'" by blast
    ultimately show ?case by blast
  qed
qed
      
lemma parPres:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   T     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"
  
  assumes PSimQ:    "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     Par:      "\<And>S T U. (S, T) \<in> Rel \<Longrightarrow> (S \<parallel> U, T \<parallel> U) \<in> Rel'"
  and     Res:      "\<And>S T x. (S, T) \<in> Rel' \<Longrightarrow> (<\<nu>x>S, <\<nu>x>T) \<in> Rel'"

  shows "P \<parallel> R \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q \<parallel> R"
proof -
  show ?thesis
  proof(induct rule: simCases)
    case(Bound a x Q')
    have "x \<sharp> P \<parallel> R" by fact
    hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
    have "Q \<parallel> R \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: parCasesB)
      case(cPar1 Q')
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      from xFreshP PSimQ QTrans obtain P' where PTrans:"P \<Longrightarrow> a<\<nu>x> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans xFreshR have "P \<parallel> R \<Longrightarrow> a<\<nu>x> \<prec> (P' \<parallel> R)" by(rule Weak_Early_Step_Semantics.Par1B)
      moreover from P'RelQ' have "(P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(rule Par)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>R \<longmapsto> a<\<nu>x> \<prec> R'\<close> \<open>x \<sharp> P\<close> have "P \<parallel> R \<longmapsto>a<\<nu>x> \<prec> (P \<parallel> R')"
        by(rule Early_Semantics.Par2B)
      hence "P \<parallel> R \<Longrightarrow> a<\<nu>x> \<prec> (P \<parallel> R')" by(rule Weak_Early_Step_Semantics.singleActionChain)
      moreover from PRelQ have "(P \<parallel> R', Q \<parallel>  R') \<in> Rel'" by(rule Par)
      ultimately show ?case by blast
    qed
  next
    case(Free \<alpha> QR')
    have "Q \<parallel> R \<longmapsto> \<alpha> \<prec> QR'" by fact
    thus ?case
    proof(induct rule: parCasesF[of _ _ _ _ _ "(P, R)"])
      case(cPar1 Q')
      have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<Longrightarrow> \<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans have Trans: "P \<parallel> R \<Longrightarrow> \<alpha> \<prec> P' \<parallel> R" by(rule Weak_Early_Step_Semantics.Par1F)
      moreover from PRel have "(P' \<parallel> R, Q' \<parallel> R) \<in> Rel'" by(blast intro: Par)
      ultimately show ?case by blast
    next
      case(cPar2 R')
      from \<open>R \<longmapsto>\<alpha> \<prec> R'\<close> have "P \<parallel> R \<longmapsto>\<alpha> \<prec> (P \<parallel> R')"
        by(rule Early_Semantics.Par2F)
      hence "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> (P \<parallel> R')" by(rule Weak_Early_Step_Semantics.singleActionChain)
      moreover from PRelQ have "(P \<parallel> R', Q \<parallel>  R') \<in> Rel'" by(rule Par)
      ultimately show ?case by blast
    next
      case(cComm1 Q' R' a b)
      have QTrans: "Q \<longmapsto> a<b> \<prec> Q'" and RTrans: "R \<longmapsto> a[b] \<prec> R'" by fact+

      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a<b> \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from RTrans have "R \<Longrightarrow>a[b] \<prec> R'" by(rule Weak_Early_Step_Semantics.singleActionChain)
      with PTrans have "P \<parallel> R \<Longrightarrow> \<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm1)
      moreover from P'RelQ' have "(P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule Par)
      ultimately show ?case by blast
    next
      case(cComm2 Q' R' a b)
      have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" and RTrans: "R \<longmapsto>a<b> \<prec> R'" by fact+
      
      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a[b] \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      from RTrans have "R \<Longrightarrow>a<b> \<prec> R'" by(rule Weak_Early_Step_Semantics.singleActionChain)
      with PTrans have "P \<parallel> R \<Longrightarrow> \<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm2)
      moreover from P'RelQ' have "(P' \<parallel> R', Q' \<parallel> R') \<in> Rel'" by(rule Par)
      ultimately show ?case by blast
    next
      case(cClose1 Q' R' a x)
      have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" and RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" by fact+
      have "x \<sharp> (P, R)" by fact
      hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by(simp add: fresh_prod)+
      
      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a<x> \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      from RTrans have "R \<Longrightarrow>a<\<nu>x> \<prec> R'" by(rule Weak_Early_Step_Semantics.singleActionChain)
      with PTrans have Trans: "P \<parallel> R \<Longrightarrow> \<tau> \<prec> <\<nu>x>(P' \<parallel> R')" using \<open>x \<sharp> P\<close>
        by(rule Weak_Early_Step_Semantics.Close1)
      moreover from P'RelQ' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> R')) \<in> Rel'"
        by(blast intro: Par Res)
      ultimately show ?case by blast
    next
      case(cClose2 Q' R' a x)
      have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and RTrans: "R \<longmapsto>a<x> \<prec> R'" by fact+
      have "x \<sharp> (P, R)" by fact
      hence xFreshR: "x \<sharp> R" and xFreshP: "x \<sharp> P" by(simp add: fresh_prod)+

      from PSimQ QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      from RTrans have "R \<Longrightarrow>a<x> \<prec> R'" by(rule Weak_Early_Step_Semantics.singleActionChain)
      with PTrans have Trans: "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')" using \<open>x \<sharp> R\<close>
        by(rule Weak_Early_Step_Semantics.Close2)
      moreover from P'RelQ' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> R')) \<in> Rel'"
        by(blast intro: Par Res)
      ultimately show ?case by blast
    qed
  qed
qed

lemma resPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   x    :: name
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     C1: "\<And>R S x. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel'"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel: "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "<\<nu>x>P \<leadsto>\<guillemotleft>Rel'\<guillemotright> <\<nu>x>Q"
proof -
  from EqvtRel' show ?thesis
  proof(induct rule: simCasesCont[of _ "(P, x)"])
    case(Bound a y Q')
    have Trans: "<\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
    have "y \<sharp> (P, x)" by fact
    hence yineqx: "y \<noteq> x" and yFreshP: "y \<sharp> P" by(simp add: fresh_prod)+
    from Trans yineqx show ?case
    proof(induct rule: resCasesB)
      case(Open Q')
      have QTrans: "Q \<longmapsto>a[x] \<prec> Q'" and aineqx: "a \<noteq> x" by fact+

      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>a[x] \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)

      from PTrans aineqx have "<\<nu>x>P \<Longrightarrow>a<\<nu>x> \<prec> P'" by(rule Weak_Early_Step_Semantics.Open)
      hence "<\<nu>x>P \<Longrightarrow>a<\<nu>y> \<prec> ([(y, x)] \<bullet> P')" using \<open>y \<sharp> P\<close> \<open>y \<noteq> x\<close>
        by(force simp add: weakTransitionAlpha abs_fresh name_swap)

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
        by(rule C1)
      ultimately show ?case by blast
    qed
  next
    case(Free \<alpha> Q')
    have QTrans: "<\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    have "\<exists>c::name. c \<sharp> (P, Q, Q', \<alpha>)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshAlpha: "c \<sharp> \<alpha>" and cFreshQ': "c \<sharp> Q'" and cFreshP: "c \<sharp> P"
      by(force simp add: fresh_prod)
    from cFreshP have "<\<nu>x>P = <\<nu>c>([(x, c)] \<bullet> P)" by(simp add: alphaRes)
    moreover have "\<exists>P'.<\<nu>c>([(x, c)] \<bullet> P) \<Longrightarrow> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
    proof -
      from QTrans cFreshQ have "<\<nu>c>([(x, c)] \<bullet> Q) \<longmapsto>\<alpha> \<prec> Q'" by(simp add: alphaRes)
      moreover have "c \<sharp> \<alpha>" by(rule cFreshAlpha)
      moreover from PSimQ EqvtRel have "([(x, c)] \<bullet> P) \<leadsto>\<guillemotleft>Rel\<guillemotright> ([(x, c)] \<bullet> Q)"
        by(blast intro: eqvtI)
      ultimately show ?thesis
        apply(induct rule: resCasesF, auto simp add: residual.inject pi.inject name_abs_eq)
        by(blast intro: Weak_Early_Step_Semantics.ResF C1 dest: simE)
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
  and     Res:     "\<And>R S x. (R, S) \<in> Rel \<Longrightarrow> (<\<nu>x>R, <\<nu>x>S) \<in> Rel"
  and     PRelQ:   "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "(resChain lst) P \<leadsto>\<guillemotleft>Rel\<guillemotright> (resChain lst) Q"
proof -
  show ?thesis
  proof(induct lst) (* Base case *)
    from PRelQ show "resChain [] P \<leadsto>\<guillemotleft>Rel\<guillemotright> resChain [] Q" by simp
  next (* Inductive step *)
    fix a lst
    assume IH: "(resChain lst P) \<leadsto>\<guillemotleft>Rel\<guillemotright> (resChain lst Q)"
    moreover from Res have "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel"
      by simp
    moreover have "Rel \<subseteq> Rel" by simp
    ultimately have "<\<nu>a>(resChain lst P) \<leadsto>\<guillemotleft>Rel\<guillemotright> <\<nu>a>(resChain lst Q)" using eqvtRel
      by(rule_tac resPres)

    thus "resChain (a # lst) P \<leadsto>\<guillemotleft>Rel\<guillemotright> resChain (a # lst) Q"
      by simp
  qed
qed

lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
 
  assumes PRelQ:    "(P, Q) \<in> Rel"
  and     Sim:      "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<guillemotleft>Rel'\<guillemotright> S"
  and     C1:       "Rel \<subseteq> Rel'"
  and     eqvtRel:  "eqvt Rel'"

  shows "!P \<leadsto>\<guillemotleft>bangRel Rel'\<guillemotright> !Q"
proof -
  let ?Sim = "\<lambda>P Rs. (\<forall>a x Q'. Rs = a<\<nu>x> \<prec> Q' \<longrightarrow> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> bangRel Rel')) \<and>
                     (\<forall>\<alpha> Q'. Rs = \<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> bangRel Rel'))"
  from eqvtRel have EqvtBangRel: "eqvt(bangRel Rel')" by(rule eqvtBangRel)
  from C1 have BRelRel': "\<And>P Q. (P, Q) \<in> bangRel Rel \<Longrightarrow> (P, Q) \<in> bangRel Rel'"
    by(auto intro: bangRelSubset)

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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)

          with QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P' \<parallel> R)"
            by(force intro: Weak_Early_Step_Semantics.Par1B)
          moreover from P'RelQ' PBRQ BRelRel' have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel'" by(blast intro: Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> bangRel Rel'" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R" and "y \<sharp> Q"
          from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q')"
            by(simp add: alphaBoundOutput)
          moreover from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          ultimately obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>y> \<prec> P'" and P'RelQ': "(P', [(x, y)] \<bullet> Q') \<in> Rel'"
            using \<open>y \<sharp> P\<close>
            by(blast dest: simE)
          from PTrans \<open>y \<sharp> R\<close> have "P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> (P' \<parallel> R)" by(force intro: Weak_Early_Step_Semantics.Par1B)
          moreover from P'RelQ' PBRQ BRelRel' have "(P' \<parallel> R, ([(x, y)] \<bullet> Q') \<parallel> !Q) \<in> bangRel Rel'" by(metis Rel.BRPar)
          with \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> have "(P' \<parallel> R, ([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) \<in> bangRel Rel'"
            by(simp add: name_fresh_fresh name_swap)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> P' \<and> (P', ([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) \<in> bangRel Rel'"
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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'" and RRel: "(P', Q') \<in> Rel'"
            by(blast dest: simE)
          
          from PTrans have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<parallel> R" by(rule Weak_Early_Step_Semantics.Par1F)
          moreover from RRel BR BRelRel' have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel'" by(metis Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> bangRel Rel'" by blast
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
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'" and R'BRQ': "(R', Q') \<in> (bangRel Rel')"
            by(metis simE)
          from RTrans xFreshP have "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> R')" by(auto intro: Weak_Early_Step_Semantics.Par2B)
          moreover from PRelQ R'BRQ' C1 have "(P \<parallel> R', Q \<parallel> Q') \<in> (bangRel Rel')" by(blast dest: Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> bangRel Rel'" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q" and "y \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R"
          from RBRQ have "?Sim R (a<\<nu>x> \<prec> Q')" by(rule IH)
          with \<open>y \<sharp> Q'\<close> have "?Sim R (a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q'))" by(simp add: alphaBoundOutput)
          with \<open>y \<sharp> R\<close> obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>y> \<prec> R'" and R'BRQ': "(R', ([(x, y)] \<bullet> Q')) \<in> (bangRel Rel')"
            by(metis simE)
          from RTrans \<open>y \<sharp> P\<close> have "P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> (P \<parallel> R')" by(auto intro: Weak_Early_Step_Semantics.Par2B)
          moreover from PRelQ R'BRQ' C1 have "(P \<parallel> R', Q \<parallel> ([(x, y)] \<bullet> Q')) \<in> (bangRel Rel')" by(blast dest: Rel.BRPar)
          with \<open>y \<sharp> Q\<close> \<open>x \<sharp> Q\<close> have "(P \<parallel> R', ([(y, x)] \<bullet> Q) \<parallel> ([(y, x)] \<bullet> Q')) \<in> (bangRel Rel')"
            by(simp add: name_swap name_fresh_fresh)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>a<\<nu>y> \<prec> P' \<and> (P', ([(y, x)] \<bullet> Q) \<parallel> ([(y, x)] \<bullet> Q')) \<in> bangRel Rel'" by blast
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
          from RBRQ IH have "\<exists>R'. R \<Longrightarrow>\<alpha> \<prec> R' \<and> (R', Q') \<in> bangRel Rel'"
            by(metis simE)
          then obtain R' where RTrans: "R \<Longrightarrow>\<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> bangRel Rel'"
            by blast

          from RTrans have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P \<parallel> R'" by(rule Weak_Early_Step_Semantics.Par2F)
          moreover from PRelQ R'RelQ' C1 have "(P \<parallel> R', Q \<parallel> Q') \<in> bangRel Rel'" by(blast dest: Rel.BRPar)
          ultimately show " \<exists>P'. P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> bangRel Rel'" by blast
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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a<b> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)
          
          from IH RBRQ have RTrans: "\<exists>R'. R \<Longrightarrow>a[b] \<prec> R' \<and> (R', Q'') \<in> bangRel Rel'"
            by(metis simE)
          then obtain R' where RTrans: "R \<Longrightarrow>a[b] \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel'"
            by blast
          
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm1)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel'" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<and> (P', Q' \<parallel> Q'') \<in> bangRel Rel'" by blast
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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from IH RBRQ have RTrans: "\<exists>R'. R \<Longrightarrow>a<b> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel'"
            by(metis simE)
          then obtain R' where RTrans: "R \<Longrightarrow>a<b> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel'"
            by blast

          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<parallel> R'" by(rule Weak_Early_Step_Semantics.Comm2)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> bangRel Rel'" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<and> (P', Q' \<parallel> Q'') \<in> bangRel Rel'" by blast
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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
             by(blast dest: simE)

           from RBRQ xFreshR IH have "\<exists>R'. R \<Longrightarrow>a<\<nu>x> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel'"
             by(metis simE)
           then obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel'"
             by blast

           from PTrans RTrans xFreshP have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
             by(rule Weak_Early_Step_Semantics.Close1)   
           moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel'"
             by(force intro: Rel.BRPar BRRes)
           ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel'" by blast
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
          from PRelQ have "P \<leadsto>\<guillemotleft>Rel'\<guillemotright> Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from RBRQ IH have "\<exists>R'.  R \<Longrightarrow>a<x> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel'"
            by auto
          then obtain R' where RTrans: "R \<Longrightarrow>a<x> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel'"
            by blast

          from PTrans RTrans xFreshR have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Close2)    
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel'"
            by(force intro: Rel.BRPar BRRes)
          ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<tau> \<prec> P' \<and> (P', <\<nu>x>(Q' \<parallel> Q'')) \<in> bangRel Rel'" by blast
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
        thus ?case by(force intro: Weak_Early_Step_Semantics.Bang)
      qed
    qed
  }

  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?thesis by(auto simp add: weakStepSimulation_def)
qed
(*
lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"
 
  assumes PRelQ:      "(P, Q) \<in> Rel"
  and     Sim:        "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> P \<leadsto><Rel'> Q"
  and     RelRel':    "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (P, Q) \<in> Rel'"
  and     eqvtRel':   "eqvt Rel'"

  shows "!P \<leadsto><bangRel Rel'> !Q"
proof -
  from eqvtRel' have EqvtBangRel': "eqvt (bangRel Rel')" by(rule eqvtBangRel)
  from RelRel' have BRelRel': "\<And>P Q. (P, Q) \<in> bangRel Rel \<Longrightarrow> (P, Q) \<in> bangRel Rel'"
    by(auto intro: bangRelSubset)
  have "\<And>Rs P. \<lbrakk>!Q \<longmapsto> Rs; (P, !Q) \<in> bangRel Rel\<rbrakk> \<Longrightarrow> weakSimStepAct P Rs P (bangRel Rel')"
  proof -
    fix Rs P
    assume "!Q \<longmapsto> Rs" and "(P, !Q) \<in> bangRel Rel"
    thus "weakSimStepAct P Rs P (bangRel Rel')"
    proof(nominal_induct avoiding: P rule: bangInduct)
      case(Par1B a x Q')
      have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and xFreshQ: "x \<sharp> Q" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelT: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        from PRelQ have PSimQ: "P \<leadsto><Rel'> Q" by(rule Sim)
        from EqvtBangRel' show ?case
        proof(induct rule: simActBoundCases)
          case BoundOutput
          with PSimQ QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                                and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)
          from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>a<\<nu>x>\<prec> (P' \<parallel> R)"
            by(rule Weak_Early_Step_Semantics.Par1B)
          moreover from P'RelQ' RBangRelT have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel'"
            by(blast intro: Rel.BRPar BRelRel')
          ultimately show ?case by blast
        qed
      qed
    next
      case(Par1F \<alpha> Q' P)
      have QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto><Rel'> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from PTrans have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P' \<parallel> R" by(rule Weak_Early_Step_Semantics.Par1F)
          moreover from P'RelQ' RBangRelQ have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel'"
            by(blast intro: Rel.BRPar BRelRel')
          ultimately show ?case by blast
        qed
      qed
    next
      case(Par2B a x Q' P)
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (a<\<nu>x> \<prec> Q') P (bangRel Rel')" by fact
      have xFreshQ: "x \<sharp> Q" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        from EqvtBangRel' show ?case
        proof(induct rule: simActBoundCases)
          case BoundOutput
          with IH RBangRelQ have "weakSimStepAct R (a<\<nu>x> \<prec> Q') R (bangRel Rel')" by blast
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'"
                                   and R'BangRelQ': "(R', Q') \<in> bangRel Rel'"
            by(simp add: weakSimStepAct_def, blast)
          
          from RTrans xFreshP have "P \<parallel> R \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> R')"
            by(auto intro: Weak_Early_Step_Semantics.Par2B)
          moreover from PRelQ R'BangRelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> (bangRel Rel')"
            by(blast intro: Rel.BRPar RelRel')
          ultimately show ?case by blast
        qed
      qed
    next
      case(Par2F \<alpha> Q' P)
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (\<alpha> \<prec> Q') P (bangRel Rel')" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from RBangRelQ have "weakSimStepAct R (\<alpha> \<prec> Q') R (bangRel Rel')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>\<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)

          from RTrans have "P \<parallel> R \<Longrightarrow>\<alpha> \<prec> P \<parallel> R'" by(rule Weak_Early_Step_Semantics.Par2F)
          moreover from PRelQ R'RelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> (bangRel Rel')" 
            by(blast intro: Rel.BRPar RelRel')
          ultimately show ?case by blast
        qed
      qed
    next
      case(Comm1 a Q' b Q'' P)
      have QTrans: "Q \<longmapsto> a<b> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (a[b] \<prec> Q'') P (bangRel Rel')" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto><Rel'> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a<b> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from RBangRelQ have "weakSimStepAct R (a[b] \<prec> Q'') R (bangRel Rel')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>a[b] \<prec> R'"
                           and R'RelQ'': "(R', Q'') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
        
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Comm1)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> (bangRel Rel')"
            by(rule Rel.BRPar)
          ultimately show ?case by blast
        qed
      qed
    next
      case(Comm2 a b Q' Q'' P)
      have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (a<b> \<prec> Q'') P (bangRel Rel')" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto><Rel'> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from RBangRelQ have "weakSimStepAct R (a<b> \<prec> Q'') R (bangRel Rel')" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>a<b> \<prec> R'" and R'BangRelQ'': "(R', Q'') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
        
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Comm2)
          moreover from P'RelQ' R'BangRelQ'' have "(P' \<parallel> R', Q' \<parallel> Q'') \<in> (bangRel Rel')"
            by(rule Rel.BRPar)
          ultimately show ?case by blast
        qed
      qed
    next
      case(Close1 a x Q' Q'' P)
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (a<\<nu>x> \<prec> Q'') P (bangRel Rel')" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshR: "x \<sharp> R" and xFreshP: "x \<sharp> P" by simp+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto><Rel'> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>a<x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)
          
          from RBangRelQ have "weakSimStepAct R (a<\<nu>x> \<prec> Q'') R (bangRel Rel')" by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<\<nu>x> \<prec> R'"
                                   and R'RelQ'': "(R', Q'') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
        
          from PTrans RTrans xFreshP xFreshR have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Close1)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> (bangRel Rel')"
            by(force intro: Rel.BRPar Rel.BRRes)
          ultimately show ?case by blast
        qed
      qed
    next
      case(Close2 a x Q' Q'' P)
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P (a<x> \<prec> Q'') P (bangRel Rel')" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto><Rel'> Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
                                          and P'RelQ': "(P', Q') \<in> Rel'"
            by(blast dest: simE)

          from RBangRelQ have "weakSimStepAct R (a<x> \<prec> Q'') R (bangRel Rel')" by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>a<x> \<prec> R'"
                                       and R'RelQ'': "(R', Q'') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
        
          from PTrans RTrans xFreshP xFreshR have "P \<parallel> R \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> R')"
            by(rule Weak_Early_Step_Semantics.Close2)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'), <\<nu>x>(Q' \<parallel> Q'')) \<in> (bangRel Rel')"
            by(force intro: Rel.BRPar Rel.BRRes)
          ultimately show ?case by blast
        qed
      qed
    next
      case(Bang Rs)
      have IH: "\<And>P. (P, Q \<parallel> !Q) \<in> bangRel Rel \<Longrightarrow> weakSimStepAct P Rs P (bangRel Rel')" by fact
      have "(P, !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        hence "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
        with PRelQ have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
        hence "weakSimStepAct (P \<parallel> !P) Rs (P \<parallel> !P) (bangRel Rel')" by(rule IH)
        thus ?case
        proof(simp (no_asm) add: weakSimStepAct_def, auto)
          fix Q' a x
          assume "weakSimStepAct (P \<parallel> !P) (a<\<nu>x> \<prec> Q') (P \<parallel> !P) (bangRel Rel')" and "x \<sharp> P"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>a<\<nu>x> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
          from PTrans have "!P \<Longrightarrow>a<\<nu>x> \<prec> P'"
            by(force intro: Weak_Early_Step_Semantics.Bang simp add: weakTransition_def)
          with P'RelQ' show "\<exists>P'. !P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> (bangRel Rel')" by blast
        next
          fix Q' \<alpha>
          assume "weakSimStepAct (P \<parallel> !P) (\<alpha> \<prec> Q') (P \<parallel> !P) (bangRel Rel')"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>\<alpha> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> (bangRel Rel')"
            by(simp add: weakSimStepAct_def, blast)
          from PTrans have "!P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.Bang)
          with P'RelQ' show "\<exists>P'. !P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> (bangRel Rel')" by blast
        qed
      qed
    qed
  qed
  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
  ultimately show ?thesis by(simp add: simDef)
qed
*)
end
