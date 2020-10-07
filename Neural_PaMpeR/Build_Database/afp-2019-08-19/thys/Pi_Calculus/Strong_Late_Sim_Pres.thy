(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Sim_Pres
  imports Strong_Late_Sim
begin

lemma tauPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "\<tau>.(P) \<leadsto>[Rel] \<tau>.(Q)"
proof -
  show "\<tau>.(P) \<leadsto>[Rel] \<tau>.(Q)"
  proof(induct rule: simCases)
    case(Bound a x Q')
    have "\<tau>.(Q) \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    hence False by auto
    thus ?case by simp
  next
    case(Free \<alpha> Q')
    have "\<tau>.(Q) \<longmapsto> \<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: tauCases)
      case cTau
      have "\<tau>.(P) \<longmapsto> \<tau> \<prec> P" by(rule Late_Semantics.Tau)
      with PRelQ show ?case by blast
    qed
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
  from \<open>a<x>.Q \<longmapsto>b\<guillemotleft>y\<guillemotright> \<prec> Q'\<close> \<open>y \<noteq> a\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close> show ?case
  proof(induct rule: inputCases)
    case cInput
    
    have "a<x>.P \<longmapsto> a<x> \<prec> P" by(rule Input) 
    hence "a<x>.P \<longmapsto> a<y> \<prec> ([(x, y)] \<bullet> P)" using \<open>y \<sharp> P\<close>
      by(simp add: alphaBoundResidual)

    moreover have "derivative ([(x, y)] \<bullet> P) ([(x, y)] \<bullet> Q) (InputS a) y Rel"
    proof(auto simp add: derivative_def)
      fix u
      show "(([(x, y)] \<bullet> P)[y::=u], ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel"
      proof(cases "y=u")
        assume "y = u"
        moreover have "([(y, x)] \<bullet> P, [(y, x)] \<bullet> Q) \<in> Rel"
        proof -
          from PRelQ have "(P[x::=x], Q[x::=x]) \<in> Rel" by blast
          hence "(P, Q) \<in> Rel" by simp
          with Eqvt show ?thesis by(rule eqvtRelI)
        qed
        ultimately show ?thesis by simp
      next
        assume yinequ: "y \<noteq> u"
        show ?thesis
        proof(cases "x = u")
          assume "x = u"
          moreover have "(([(y, x)] \<bullet> P)[y::=x], ([(y, x)] \<bullet> Q)[y::=x]) \<in> Rel"
          proof -
            from PRelQ have "(P[x::=y], Q[x::=y]) \<in> Rel" by blast
            with Eqvt have "([(y, x)] \<bullet> (P[x::=y]), [(y, x)] \<bullet> (Q[x::=y])) \<in> Rel"
              by(rule eqvtRelI)
            with \<open>y \<noteq> x\<close> show ?thesis
              by(simp add: eqvt_subs name_calc)
          qed
          ultimately show ?thesis by simp
        next
          assume xinequ: "x \<noteq> u"
          hence "(([(y, x)] \<bullet> P)[y::=u], ([(y, x)] \<bullet> Q)[y::=u]) \<in> Rel"
          proof -
            from PRelQ have "(P[x::=u], Q[x::=u]) \<in> Rel" by blast
            with Eqvt have "([(y, x)] \<bullet> (P[x::=u]), [(y, x)] \<bullet> (Q[x::=u])) \<in> Rel"
              by(rule eqvtRelI)
            with \<open>y \<noteq> x\<close>  xinequ yinequ show ?thesis
              by(simp add: eqvt_subs name_calc)
          qed
          thus ?thesis by simp
        qed
      qed
    qed
    
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> Q')
  have "a<x>.Q \<longmapsto> \<alpha> \<prec> Q'" by fact
  hence False by auto
  thus ?case by blast
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
proof -
  show ?thesis
  proof(induct rule: simCases)
    case(Bound c x Q')
    have "a{b}.Q \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    hence False by auto
    thus ?case by simp
  next
    case(Free \<alpha> Q')
    have "a{b}.Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: outputCases)
      case cOutput
      have "a{b}.P \<longmapsto> a[b] \<prec> P" by(rule Late_Semantics.Output)
      with PRelQ show ?case by blast
    qed
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
  and     "Rel \<subseteq> Rel'"

  shows "[a\<frown>b]P \<leadsto>[Rel'] [a\<frown>b]Q"
proof -
  show ?thesis
  proof(induct rule: simCases)
    case(Bound c x Q')
    have "x \<sharp>  [a\<frown>b]P" by fact
    hence xFreshP: "x \<sharp> P" by simp
    have "[a\<frown>b]Q \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: matchCases)
      case cMatch
      have "Q \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
      with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'"
                                     and Pderivative: "derivative P' Q' c x Rel"
        by(blast dest: simE)

      from PTrans have "[a\<frown>a]P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> P'" by(rule Late_Semantics.Match)
      moreover from Pderivative \<open>Rel \<subseteq> Rel'\<close> have "derivative P' Q' c x Rel'"
        by(cases c) (auto simp add: derivative_def)
      ultimately show ?case by blast
    qed
  next
    case(Free \<alpha> Q')
    have "[a\<frown>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: matchCases)
      case cMatch
      have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'"
                             and PRel: "(P', Q') \<in> Rel"
          by(blast dest: simE)
      from PTrans have "[a\<frown>a]P \<longmapsto>\<alpha> \<prec> P'" by(rule Late_Semantics.Match)
      with PRel \<open>Rel \<subseteq> Rel'\<close> show ?case by blast
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

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     "Rel \<subseteq> Rel'"

  shows "[a\<noteq>b]P \<leadsto>[Rel'] [a\<noteq>b]Q"
proof(induct rule: simCases)
  case(Bound c x Q')
  have "x \<sharp> [a\<noteq>b]P" by fact
  hence xFreshP: "x \<sharp> P" by simp
  from \<open>[a\<noteq>b]Q \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> Q'\<close> show ?case
  proof(induct rule: mismatchCases)
    case cMismatch
    have "Q \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P' where PTrans: "P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'"
                                   and Pderivative: "derivative P' Q' c x Rel"
      by(blast dest: simE)

    from PTrans \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<longmapsto> c\<guillemotleft>x\<guillemotright> \<prec> P'" by(rule Late_Semantics.Mismatch)
    moreover from Pderivative \<open>Rel \<subseteq> Rel'\<close> have "derivative P' Q' c x Rel'"
      by(cases c) (auto simp add: derivative_def)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> Q')
  have "[a\<noteq>b]Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: mismatchCases)
    case cMismatch
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'"
                           and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans \<open>a \<noteq> b\<close> have "[a\<noteq>b]P \<longmapsto>\<alpha> \<prec> P'" by(rule Late_Semantics.Mismatch)
    with PRel \<open>Rel \<subseteq> Rel'\<close> show ?case by blast
  qed
qed

lemma sumPres:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     "Id \<subseteq> Rel'"
  and     "Rel \<subseteq> Rel'"

  shows "P \<oplus> R \<leadsto>[Rel'] Q \<oplus> R"
proof -
  show ?thesis
  proof(induct rule: simCases)
    case(Bound a x QR)
    have "x \<sharp> P \<oplus> R" by fact
    hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
    have "Q \<oplus> R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> QR" by fact
    thus ?case
    proof(induct rule: sumCases)
      case cSum1
      have "Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> QR" by fact
      with xFreshP PSimQ obtain P' where PTrans: "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'"
                                     and Pderivative: "derivative P' QR a x Rel"
        by(blast dest: simE)

      from PTrans have "P \<oplus> R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'" by(rule Late_Semantics.Sum1)
      moreover from Pderivative \<open>Rel \<subseteq> Rel'\<close> have "derivative P' QR a x Rel'"
        by(cases a) (auto simp add: derivative_def)
      ultimately show ?case by blast
    next
      case cSum2
      from \<open>R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> QR\<close> have "P \<oplus> R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> QR" by(rule Sum2)
      thus ?case using \<open>Id \<subseteq> Rel'\<close> by(blast intro: derivativeReflexive)
    qed
  next
    case(Free \<alpha> QR)
    have "Q \<oplus> R \<longmapsto>\<alpha> \<prec> QR" by fact
    thus ?case
    proof(induct rule: sumCases)
      case cSum1
      have "Q \<longmapsto>\<alpha> \<prec> QR" by fact
      with PSimQ obtain P' where PTrans: "P \<longmapsto>\<alpha> \<prec> P'" and PRel: "(P', QR) \<in> Rel" 
        by(blast dest: simE)
      from PTrans have "P \<oplus> R \<longmapsto>\<alpha> \<prec> P'" by(rule Late_Semantics.Sum1)
      with PRel \<open>Rel \<subseteq> Rel'\<close> show ?case by blast
    next
      case cSum2
      from \<open>R \<longmapsto>\<alpha> \<prec> QR\<close> have "P \<oplus> R \<longmapsto>\<alpha> \<prec> QR" by(rule Sum2)
      thus ?case using \<open>Id \<subseteq> Rel'\<close> by(blast intro: derivativeReflexive)
    qed
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
  and     RSimT:    "R \<leadsto>[Rel'] T"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     RRel'T:   "(R, T) \<in> Rel'"
  and     Par:      "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Rel'\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel''"
  and     Res:      "\<And>P Q a. (P, Q) \<in> Rel'' \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel''"
  and     EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"
  and     EqvtRel'': "eqvt Rel''"

  shows "P \<parallel> R \<leadsto>[Rel''] Q \<parallel> T"
using EqvtRel''
proof(induct rule: simCasesCont[where C="()"])
  case(Bound a x Q')
  have "x \<sharp> P \<parallel> R" and "x \<sharp> Q \<parallel> T" by fact+
  hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" and "x \<sharp> Q" and "x \<sharp> T" by simp+
  have QTTrans: "Q \<parallel> T \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
  thus ?case using \<open>x \<sharp> Q\<close> \<open>x \<sharp> T\<close>
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    have QTrans: "Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'" and xFreshT: "x \<sharp> T" by fact+
      
    from xFreshP PSimQ QTrans obtain P' where PTrans:"P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'"
                                          and Pderivative: "derivative P' Q' a x Rel"
      by(blast dest: simE)
    from PTrans xFreshR have "P \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> R" by(rule Late_Semantics.Par1B)
    moreover from Pderivative xFreshR xFreshT RRel'T have "derivative (P' \<parallel> R) (Q' \<parallel> T) a x Rel''"
      by(cases a, auto intro: Par simp add: derivative_def forget)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    have TTrans: "T \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> T'" and xFreshQ: "x \<sharp> Q" by fact+
    
    from xFreshR RSimT TTrans obtain R' where RTrans:"R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> R'"
                                          and Rderivative: "derivative R' T' a x Rel'"
      by(blast dest: simE)
    from RTrans xFreshP have ParTrans: "P \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> R'" by(rule Late_Semantics.Par2B)      
    moreover from Rderivative xFreshP xFreshQ PRelQ have "derivative (P \<parallel> R') (Q \<parallel>  T') a x Rel''"
      by(cases a, auto intro: Par simp add: derivative_def forget)
    ultimately show ?case by blast
  qed
next
  case(Free \<alpha> QT')
  have QTTrans: "Q \<parallel> T \<longmapsto> \<alpha> \<prec> QT'" by fact
  thus ?case using PSimQ RSimT PRelQ RRel'T
  proof(induct rule: parCasesF[where C="(P, R)"])
    case(cPar1 Q')
    have RRel'T: "(R, T) \<in> Rel'" by fact
    have "P \<leadsto>[Rel] Q" and "Q \<longmapsto> \<alpha> \<prec> Q'" by fact+
    then obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have Trans: "P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<parallel> R" by(rule Late_Semantics.Par1F)
    moreover from PRel RRel'T have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(blast intro: Par)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    have PRelQ: "(P, Q) \<in> Rel" by fact
    have "R \<leadsto>[Rel'] T" and "T \<longmapsto> \<alpha> \<prec> T'" by fact+
    then obtain R' where RTrans: "R \<longmapsto> \<alpha> \<prec> R'" and RRel: "(R', T') \<in> Rel'"
      by(blast dest: simE)
    from RTrans have Trans: "P \<parallel> R \<longmapsto> \<alpha> \<prec> P \<parallel> R'" by(rule Late_Semantics.Par2F)
    moreover from PRelQ RRel have "(P \<parallel> R', Q \<parallel> T') \<in> Rel''" by(blast intro: Par)
    ultimately show ?case by blast
  next
    case(cComm1 Q' T' a b x)
    from \<open>x \<sharp> (P, R)\<close> have "x \<sharp> P" by simp
    with \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto> a<x> \<prec> Q'\<close> \<open>x \<sharp> P\<close>
    obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'" 
                and Pderivative: "derivative P' Q' (InputS a) x Rel"
      by(blast dest: simE)
    from Pderivative have PRel: "(P'[x::=b], Q'[x::=b]) \<in> Rel" by(simp add: derivative_def)
      
    have "R \<leadsto>[Rel'] T" and "T \<longmapsto> a[b] \<prec> T'" by fact+
    then obtain R' where RTrans: "R \<longmapsto>a[b] \<prec> R'" and RRel: "(R', T') \<in> Rel'"
      by(blast dest: simE)
      
    from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P'[x::=b] \<parallel> R'" by(rule Late_Semantics.Comm1)
    moreover from PRel RRel have "(P'[x::=b] \<parallel> R', Q'[x::=b] \<parallel> T') \<in> Rel''" by(blast intro: Par)
    ultimately show ?case by blast
  next
    case(cComm2 Q' T' a b x)
    have "P \<leadsto>[Rel] Q" and "Q \<longmapsto>a[b] \<prec> Q'" by fact+
    then obtain P' where PTrans: "P \<longmapsto>a[b] \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    
    from \<open>x \<sharp> (P, R)\<close> have "x \<sharp> R" by simp
    with \<open>R \<leadsto>[Rel'] T\<close> \<open>T \<longmapsto>a<x> \<prec> T'\<close>
    obtain R' where RTrans: "R \<longmapsto>a<x> \<prec> R'"
                and Rderivative: "derivative R' T' (InputS a) x Rel'"
      by(blast dest: simE)
    from Rderivative have RRel: "(R'[x::=b], T'[x::=b]) \<in> Rel'" by(simp add: derivative_def)
      
    from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<parallel> R'[x::=b]" by(rule Late_Semantics.Comm2)
    moreover from PRel RRel have "(P' \<parallel> R'[x::=b], Q' \<parallel> T'[x::=b]) \<in> Rel''" by(blast intro: Par)
    ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', Q' \<parallel> T'[x::=b]) \<in> Rel''" by blast
  next
    case(cClose1 Q' T' a x y)
    from \<open>x \<sharp> (P, R)\<close> have "x \<sharp> P" by simp
    with \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto>a<x> \<prec> Q'\<close>
    obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'"
                and Pderivative: "derivative P' Q' (InputS a) x Rel"
      by(blast dest: simE)
    from Pderivative have PRel: "(P'[x::=y], Q'[x::=y]) \<in> Rel" by(simp add: derivative_def)
      
    from \<open>y \<sharp> (P, R)\<close> have "y \<sharp> R" and "y \<sharp> P" by simp+
    from \<open>R \<leadsto>[Rel'] T\<close> \<open>T \<longmapsto>a<\<nu>y> \<prec> T'\<close> \<open>y \<sharp> R\<close>
    obtain R' where RTrans: "R \<longmapsto>a<\<nu>y> \<prec> R'"
                and Rderivative: "derivative R' T' (BoundOutputS a) y Rel'"
      by(blast dest: simE)
    from Rderivative have RRel: "(R', T') \<in> Rel'" by(simp add: derivative_def)
    
    from PTrans RTrans \<open>y \<sharp> P\<close> have Trans: "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> R')"
      by(rule Late_Semantics.Close1)
    moreover from PRel RRel have "(<\<nu>y>(P'[x::=y] \<parallel> R'), <\<nu>y>(Q'[x::=y] \<parallel> T')) \<in> Rel''"
      by(blast intro: Par Res)
    ultimately show ?case by blast
  next
    case(cClose2 Q' T' a x y)
    from \<open>y \<sharp> (P, R)\<close> have "y \<sharp> P" and "y \<sharp> R" by simp+
    from \<open>P \<leadsto>[Rel] Q\<close> \<open>Q \<longmapsto>a<\<nu>y> \<prec> Q'\<close> \<open>y \<sharp> P\<close>
    obtain P' where PTrans: "P \<longmapsto>a<\<nu>y> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(force dest: simE simp add: derivative_def)
    
    from \<open>x \<sharp> (P, R)\<close> have "x \<sharp> R" by simp+
    with \<open>R \<leadsto>[Rel'] T\<close> \<open>T \<longmapsto>a<x> \<prec> T'\<close>
    obtain R' where RTrans: "R \<longmapsto>a<x> \<prec> R'"
                and R'Rel'T': "(R'[x::=y], T'[x::=y]) \<in> Rel'" 
      by(force dest: simE simp add: derivative_def)
      
    from PTrans RTrans \<open>y \<sharp> R\<close> have Trans: "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> R'[x::=y])"
      by(rule Close2)
    moreover from P'RelQ' R'Rel'T' have "(<\<nu>y>(P' \<parallel> R'[x::=y]), <\<nu>y>(Q' \<parallel> T'[x::=y])) \<in> Rel''"
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
  and     Par:      "\<And>P Q R. (P, Q) \<in> Rel \<Longrightarrow> (P \<parallel> R, Q \<parallel> R) \<in> Rel'"
  and     Res:      "\<And>P Q a. (P, Q) \<in> Rel' \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel'"
  and     EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "P \<parallel> R \<leadsto>[Rel'] Q \<parallel> R"
proof -
  note PSimQ 
  moreover have RSimR: "R \<leadsto>[Id] R" by(auto intro: reflexive)
  moreover note PRelQ moreover have "(R, R) \<in> Id" by auto
  moreover from Par have "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Id\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel'"
    by auto
  moreover note Res \<open>eqvt Rel\<close>
  moreover have "eqvt Id" by(auto simp add: eqvt_def)
  ultimately show ?thesis using EqvtRel' by(rule parCompose)
qed

lemma resDerivative:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: subject
  and   x    :: name
  and   y    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"
  
  assumes Der: "derivative P Q a x Rel"
  and     Rel: "\<And>(P::pi) (Q::pi) (x::name). (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> Rel'"
  and     Eqv: "eqvt Rel"

  shows "derivative (<\<nu>y>P) (<\<nu>y>Q) a x Rel'"
proof -
  from Der Rel show ?thesis
  proof(cases a, auto simp add: derivative_def)
    fix u
    assume A1: "\<forall>u. (P[x::=u], Q[x::=u]) \<in> Rel"
    show "((<\<nu>y>P)[x::=u], (<\<nu>y>Q)[x::=u]) \<in> Rel'" 
    proof(cases "x=y")
      assume xeqy: "x=y"

      from A1 have "(P[x::=x], Q[x::=x]) \<in> Rel" by blast
      hence L1: "(<\<nu>y>P, <\<nu>y>Q) \<in> Rel'" by(force intro: Rel)

      have "y \<sharp> <\<nu>y>P" and "y \<sharp> <\<nu>y>Q" by(simp only: freshRes)+
      hence "(<\<nu>y>P)[y::=u] = <\<nu>y>P" and "(<\<nu>y>Q)[y::=u] = <\<nu>y>Q" by(simp add: forget)+

      with L1 xeqy show ?thesis by simp
    next
      assume xineqy: "x\<noteq>y"

      show ?thesis
      proof(cases "y=u")
        assume yequ: "y=u"
      
        have "\<exists>(c::name). c \<sharp> (P, Q, x, y)" by(blast intro: name_exists_fresh)
        then obtain c where cFreshP: "c \<sharp> P" and cFreshQ: "c \<sharp> Q" and cineqx: "c \<noteq> x" and cineqy: "y \<noteq> c"
          by(force simp add: fresh_prod name_fresh)
        
        from A1 have "(P[x::=c], Q[x::=c]) \<in> Rel" by blast
        with Eqv have "([(y, c)] \<bullet> (P[x::=c]), [(y, c)] \<bullet> (Q[x::=c])) \<in> Rel" by(rule eqvtRelI)
        with xineqy cineqx cineqy have "(([(y, c)] \<bullet> P)[x::=y], ([(y, c)] \<bullet> Q)[x::=y]) \<in> Rel"
          by(simp add: eqvt_subs name_calc)
        hence "(<\<nu>c>(([(y, c)] \<bullet> P)[x::=y]), <\<nu>c>(([(y, c)] \<bullet> Q)[x::=y])) \<in> Rel'" by(rule Rel)
        with cineqx cineqy have "((<\<nu>c>(([(y, c)] \<bullet> P)))[x::=y], (<\<nu>c>(([(y, c)] \<bullet> Q)))[x::=y])\<in> Rel'" by simp
        moreover from cFreshP cFreshQ have "<\<nu>c>([(y, c)] \<bullet> P) = <\<nu>y>P" and "<\<nu>c>([(y, c)] \<bullet> Q) = <\<nu>y>Q"
          by(simp add: alphaRes)+
        ultimately show ?thesis using yequ by simp
      next
        assume yinequ: "y \<noteq> u"
        from A1 have "(P[x::=u], Q[x::=u]) \<in> Rel" by blast
        hence "(<\<nu>y>(P[x::=u]), <\<nu>y>(Q[x::=u])) \<in> Rel'" by(rule Rel)
        with xineqy yinequ show ?thesis by simp
      qed
    qed
  qed
qed

lemma resPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   x    :: name
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     ResRel: "\<And>(P::pi) (Q::pi) (x::name). (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> Rel'"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel: "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "<\<nu>x>P \<leadsto>[Rel'] <\<nu>x>Q"
using EqvtRel'
proof(induct rule: resSimCases[of _ _ _ _ "(P, x)"])
  case(BoundOutput Q' a)
  have QTrans: "Q \<longmapsto>a[x] \<prec> Q'" and aineqx: "a \<noteq> x" by fact+
  
  from PSimQ QTrans obtain P' where PTrans: "P \<longmapsto> a[x] \<prec> P'"
                                and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: simE)
  
  from PTrans aineqx have "<\<nu>x>P \<longmapsto>a<\<nu>x> \<prec> P'" by(rule Late_Semantics.Open)
  moreover from P'RelQ' RelRel' have "(P', Q') \<in> Rel'" by force
  ultimately show ?case by blast
next
  case(BoundR Q' a y)
  have QTrans: "Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> Q'" and xFresha: "x \<sharp> a" by fact+
  have "y \<sharp> (P, x)" by fact 
  hence yFreshP: "y \<sharp> P" and yineqx: "y \<noteq> x" by(simp add: fresh_prod)+
  
  from PSimQ yFreshP QTrans  obtain P' where PTrans: "P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'"
                                         and Pderivative: "derivative P' Q' a y Rel"
    by(blast dest: simE)
  from PTrans xFresha yineqx have ResTrans: "<\<nu>x>P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> <\<nu>x>P'"
    by(blast intro: Late_Semantics.ResB)
  moreover from Pderivative ResRel EqvtRel have "derivative (<\<nu>x>P') (<\<nu>x>Q') a y Rel'"
    by(rule resDerivative)
  
  ultimately show ?case by blast
next
  case(FreeR Q' \<alpha>)
  have QTrans: "Q \<longmapsto> \<alpha> \<prec> Q'" and xFreshAlpha: "(x::name) \<sharp> \<alpha>" by fact+
      
  from QTrans PSimQ obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'"
                                and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: simE)

  from PTrans xFreshAlpha have "<\<nu>x>P \<longmapsto>\<alpha> \<prec> <\<nu>x>P'" by(rule Late_Semantics.ResF)
  moreover from P'RelQ' have "(<\<nu>x>P', <\<nu>x>Q') \<in> Rel'" by(rule ResRel)
  ultimately show ?case by blast
qed

lemma resChainI:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   xs  :: "name list"

  assumes PRelQ:   "P \<leadsto>[Rel] Q"
  and     eqvtRel: "eqvt Rel"
  and     Res:     "\<And>P Q x. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> Rel"

  shows "(resChain xs) P \<leadsto>[Rel] (resChain xs) Q"
proof(induct xs) (* Base case *)
  from PRelQ show "resChain [] P \<leadsto>[Rel] resChain [] Q" by simp
next (* Inductive step *)
  fix x xs
  assume IH: "(resChain xs P) \<leadsto>[Rel] (resChain xs Q)"
  moreover note Res
  moreover have "Rel \<subseteq> Rel" by simp
  ultimately have "<\<nu>x>(resChain xs P) \<leadsto>[Rel] <\<nu>x>(resChain xs Q)" using eqvtRel
    by(rule_tac resPres) 
  
  thus "resChain (x # xs) P \<leadsto>[Rel] resChain (x # xs) Q"
    by simp
qed

lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
 
  assumes PRelQ:    "(P, Q) \<in> Rel"
  and     Sim:      "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> P \<leadsto>[Rel] Q"
  and     eqvtRel:  "eqvt Rel"

  shows "!P \<leadsto>[bangRel Rel] !Q"
proof -
  let ?Sim = "\<lambda>P Rs. (\<forall>a x Q'. Rs = a\<guillemotleft>x\<guillemotright> \<prec> Q' \<longrightarrow> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' Q' a x (bangRel Rel))) \<and>
                     (\<forall>\<alpha> Q'. Rs = \<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> bangRel Rel))"
  from eqvtRel have EqvtBangRel: "eqvt(bangRel Rel)" by(rule eqvtBangRel)

  {
    fix Pa Rs
    assume "!Q \<longmapsto> Rs" and "(Pa, !Q) \<in> bangRel Rel"
    hence "?Sim Pa Rs" using PRelQ
    proof(nominal_induct avoiding: Pa P rule: bangInduct)
      case(cPar1B a x Q' Pa P)
      have QTrans: "Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" by fact+
      thus "?Sim Pa (a\<guillemotleft>x\<guillemotright> \<prec> (Q' \<parallel> !Q))"
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        have PBRQ: "(R, !Q) \<in> bangRel Rel" by fact
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        show ?case 
        proof(auto simp add: residual.inject alpha')
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)

          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'" and P'RelQ': "derivative P' Q' a x Rel"
            by(blast dest: simE)

          from PTrans xFreshR have "P \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> R)"
            by(force intro: Late_Semantics.Par1B)
          moreover from P'RelQ' PBRQ \<open>x \<sharp> Q\<close> \<open>x \<sharp> R\<close> have "derivative (P' \<parallel> R) (Q' \<parallel> !Q) a x (bangRel Rel)"
            by(cases a) (auto simp add: derivative_def forget intro: Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' (Q' \<parallel> !Q) a x (bangRel Rel)" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R" and "y \<sharp> Q"
          from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> ([(x, y)] \<bullet> Q')"
            by(simp add: alphaBoundResidual)
          moreover from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          ultimately obtain P' where PTrans: "P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'" and P'RelQ': "derivative P' ([(x, y)] \<bullet> Q') a y Rel"
            using \<open>y \<sharp> P\<close>
            by(blast dest: simE)
          from PTrans \<open>y \<sharp> R\<close> have "P \<parallel> R \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> (P' \<parallel> R)" by(force intro: Late_Semantics.Par1B)
          moreover from P'RelQ' PBRQ \<open>y \<sharp> Q\<close> \<open>y \<sharp> R\<close> have "derivative (P' \<parallel> R) (([(x, y)] \<bullet> Q') \<parallel> !Q) a y (bangRel Rel)"
            by(cases a) (auto simp add: derivative_def forget intro: Rel.BRPar)
          with \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> have "derivative (P' \<parallel> R) (([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) a y (bangRel Rel)"
            by(simp add: name_fresh_fresh name_swap)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P' \<and> derivative P' (([(y, x)] \<bullet> Q') \<parallel> !([(y, x)] \<bullet> Q)) a y (bangRel Rel)"
            by blast
        qed
      qed
    next
      case(cPar1F \<alpha> Q' Pa P)
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
            by(blast dest: simE)
          
          from PTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<parallel> R" by(rule Par1F)
          moreover from RRel BR have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q' \<parallel> !Q) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(cPar2B a x Q' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a\<guillemotleft>x\<guillemotright> \<prec> Q')" by simp
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" by fact+
      thus "?Sim Pa (a\<guillemotleft>x\<guillemotright> \<prec> (Q \<parallel> Q'))"
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+

        from EqvtBangRel \<open>x \<sharp> Q\<close> show "?Sim (P \<parallel> R) (a\<guillemotleft>x\<guillemotright> \<prec> (Q \<parallel> Q'))"
        proof(auto simp add: residual.inject alpha' name_fresh_fresh)
          from RBRQ have "?Sim R (a\<guillemotleft>x\<guillemotright> \<prec> Q')" by(rule IH)
          with xFreshR obtain R' where RTrans: "R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> R'" and R'BRQ': "derivative R' Q' a x (bangRel Rel)"
            by(auto simp add: residual.inject)
          from RTrans xFreshP have "P \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> R')" by(auto intro: Par2B)
          moreover from PRelQ R'BRQ' \<open>x \<sharp> Q\<close> \<open>x \<sharp> P\<close> have "derivative (P \<parallel> R') (Q \<parallel> Q') a x (bangRel Rel)" 
            by(cases a) (auto simp add: derivative_def forget intro: Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<and> derivative P' (Q \<parallel> Q') a x (bangRel Rel)" by blast
        next
          fix y
          assume "(y::name) \<sharp> Q" and "y \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> R"
          from RBRQ have "?Sim R (a\<guillemotleft>x\<guillemotright> \<prec> Q')" by(rule IH)
          with \<open>y \<sharp> Q'\<close> have "?Sim R (a\<guillemotleft>y\<guillemotright> \<prec> ([(x, y)] \<bullet> Q'))" by(simp add: alphaBoundResidual)
          with \<open>y \<sharp> R\<close> obtain R' where RTrans: "R \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> R'" and R'BRQ': "derivative R' ([(x, y)] \<bullet> Q') a y (bangRel Rel)"
            by(auto simp add: residual.inject)
          from RTrans \<open>y \<sharp> P\<close> have "P \<parallel> R \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> (P \<parallel> R')" by(auto intro: Par2B)
          moreover from PRelQ R'BRQ' \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> have "derivative (P \<parallel> R') (Q \<parallel> ([(x, y)] \<bullet> Q')) a y (bangRel Rel)" 
            by(cases a) (auto simp add: derivative_def forget intro: Rel.BRPar)
          hence "derivative (P \<parallel> R') (Q \<parallel> ([(y, x)] \<bullet> Q')) a y (bangRel Rel)"
            by(simp add: name_swap)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> a\<guillemotleft>y\<guillemotright> \<prec> P' \<and> derivative P' (Q \<parallel> ([(y, x)] \<bullet> Q')) a y (bangRel Rel)" by blast
        qed
      qed
    next
      case(cPar2F \<alpha> Q' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (\<alpha> \<prec> Q')" by simp
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(auto simp add: residual.inject)
          from RBRQ IH have "\<exists>R'. R \<longmapsto> \<alpha> \<prec> R' \<and> (R', Q') \<in> bangRel Rel"
            by(metis simE)
          then obtain R' where RTrans: "R \<longmapsto> \<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> bangRel Rel"
            by blast

          from RTrans have "P \<parallel> R \<longmapsto> \<alpha> \<prec> P \<parallel> R'" by(rule Par2F)
          moreover from PRelQ R'RelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show " \<exists>P'. P \<parallel> R \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q \<parallel> Q') \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(cComm1 a x Q' b Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a[b] \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case using \<open>x \<sharp> Pa\<close>
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        from \<open>x \<sharp> P \<parallel> R\<close> have "x \<sharp> P" and "x \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans \<open>x \<sharp> P\<close> obtain P' where PTrans: "P \<longmapsto> a<x> \<prec> P'" and P'RelQ': "(P'[x::=b], Q'[x::=b]) \<in> Rel"
            by(drule_tac simE) (auto simp add: derivative_def)
          
          from IH RBRQ have RTrans: "\<exists>R'. R \<longmapsto> a[b] \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
            by(auto simp add: derivative_def)
          then obtain R' where RTrans: "R \<longmapsto> a[b] \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
            by blast
          
          from PTrans RTrans have "P \<parallel> R \<longmapsto>\<tau> \<prec> P'[x::=b] \<parallel> R'" by(rule Comm1)
          moreover from P'RelQ' R'RelQ'' have "(P'[x::=b] \<parallel> R', Q'[x::=b] \<parallel> Q'') \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', Q'[x::=b] \<parallel> Q'') \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(cComm2 a b Q' x Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a<x> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a[b] \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case using \<open>x \<sharp> Pa\<close>
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        from \<open>x \<sharp> P \<parallel> R\<close> have "x \<sharp> P" and "x \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<longmapsto> a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from IH RBRQ \<open>x \<sharp> R\<close> have RTrans: "\<exists>R'. R \<longmapsto> a<x> \<prec> R' \<and> (R'[x::=b], Q''[x::=b]) \<in> bangRel Rel"
            by(fastforce simp add: derivative_def residual.inject)
          then obtain R' where RTrans: "R \<longmapsto> a<x> \<prec> R'" and R'RelQ'': "(R'[x::=b], Q''[x::=b]) \<in> bangRel Rel"
            by blast

          from PTrans RTrans have "P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<parallel> R'[x::=b]" by(rule Comm2)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R'[x::=b], Q' \<parallel> Q''[x::=b]) \<in> bangRel Rel" by(rule Rel.BRPar)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', Q' \<parallel> (Q''[x::=b])) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(cClose1 a x Q' y Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<longrightarrow> ?Sim Pa (a<\<nu>y> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      moreover have xFreshPa: "x \<sharp> Pa" by fact
      ultimately show ?case using \<open>y \<sharp> Pa\<close>
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" and "y \<sharp> P \<parallel> R" by fact+
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" and "y \<sharp> R" and "y \<sharp> P" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto>a<x> \<prec> P'" and P'RelQ': "(P'[x::=y], Q'[x::=y]) \<in> Rel"
            by(fastforce dest: simE simp add: derivative_def)

           from RBRQ \<open>y \<sharp> R\<close> IH have "\<exists>R'. R \<longmapsto>a<\<nu>y> \<prec> R' \<and> (R', Q'') \<in> bangRel Rel"
             by(auto simp add: residual.inject derivative_def)
           then obtain R' where RTrans: "R \<longmapsto>a<\<nu>y> \<prec> R'" and R'RelQ'': "(R', Q'') \<in> bangRel Rel"
             by blast

           from PTrans RTrans \<open>y \<sharp> P\<close> have "P \<parallel> R \<longmapsto>\<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> R')"
             by(rule Close1)     
           moreover from P'RelQ' R'RelQ'' have "(<\<nu>y>(P'[x::=y] \<parallel> R'), <\<nu>y>(Q'[x::=y] \<parallel> Q'')) \<in> bangRel Rel"
             by(force intro: Rel.BRPar BRRes)
           ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', <\<nu>y>(Q'[x::=y] \<parallel> Q'')) \<in> bangRel Rel" by blast
         qed
      qed
    next
      case(cClose2 a x Q' y Q'' Pa P)
      hence IH: "\<And>Pa. (Pa, !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa (a<y> \<prec> Q'')" by simp
      have QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" by fact
      have "(Pa, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> Pa" and "y \<sharp> Pa" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBRQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" and "y \<sharp> P \<parallel> R" by fact+
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" and "y \<sharp> R" by simp+
        show ?case
        proof(auto simp add: residual.inject)
          from PRelQ have "P \<leadsto>[Rel] Q" by(rule Sim)
          with QTrans xFreshP obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(fastforce dest: simE simp add: derivative_def)

          from RBRQ IH \<open>y \<sharp> R\<close> have "\<exists>R'.  R \<longmapsto>a<y> \<prec> R' \<and> (R'[y::=x], Q''[y::=x]) \<in> bangRel Rel"
            by(fastforce simp add: derivative_def residual.inject)
          then obtain R' where RTrans: "R \<longmapsto>a<y> \<prec> R'" and R'RelQ'': "(R'[y::=x], Q''[y::=x]) \<in> bangRel Rel"
            by blast

          from PTrans RTrans xFreshR have "P \<parallel> R \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> R'[y::=x])"
            by(rule Close2)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>x>(P' \<parallel> R'[y::=x]), <\<nu>x>(Q' \<parallel> Q''[y::=x])) \<in> bangRel Rel"
            by(force intro: Rel.BRPar BRRes)
          ultimately show "\<exists>P'. P \<parallel> R \<longmapsto> \<tau> \<prec> P' \<and> (P', <\<nu>x>(Q' \<parallel> Q''[y::=x])) \<in> bangRel Rel" by blast
        qed
      qed
    next
      case(cBang Rs Pa P)
      hence IH: "\<And>Pa. (Pa, Q \<parallel> !Q) \<in> bangRel Rel \<Longrightarrow> ?Sim Pa Rs" by simp
      have "(Pa, !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        hence "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
        with PRelQ have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule BRPar)
        with IH have "?Sim (P \<parallel> !P) Rs" by simp
        thus ?case by(force intro: Bang)
      qed
    qed
  }

  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule BRBang) 
  ultimately show ?thesis by(auto simp add: simulation_def)
qed

end
