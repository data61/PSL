(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Sim_Pres
  imports Weak_Late_Sim
begin

lemma tauPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PRelQ: "(P, Q) \<in> Rel"

  shows "\<tau>.(P) \<leadsto>\<^sup>^<Rel> \<tau>.(Q)"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "\<tau>.(Q) \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  hence False by auto
  thus ?case by simp
next
  case(Input Q' a x)
  have "\<tau>.(Q) \<longmapsto>a<x> \<prec> Q'" by fact
  hence False by auto
  thus ?case by simp
next
  case(Free Q' \<alpha>)
  have "\<tau>.(Q) \<longmapsto>(\<alpha> \<prec> Q')" by fact
  thus ?case using PRelQ
  proof(induct rule: tauCases, auto simp add: pi.inject residual.inject)
    have "\<tau>.(P) \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec> P" by(rule Tau)
    moreover assume "(P, Q') \<in> Rel"
    ultimately show "\<exists>P'. \<tau>.(P) \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec> P' \<and> (P', Q') \<in> Rel" by blast
  qed
qed

lemma inputPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   x    :: name
  and   Rel  :: "(pi \<times> pi) set"

  assumes PRelQ: "\<forall>y. (P[x::=y], Q[x::=y]) \<in> Rel"
  and     Eqvt: "eqvt Rel"

  shows "a<x>.P \<leadsto>\<^sup>^<Rel> a<x>.Q"
proof -
  show ?thesis using Eqvt
  proof(induct rule: simCasesCont[of _ "(P, a, x, Q)"])
    case(Bound Q' b y)
    have "a<x>.Q \<longmapsto>b<\<nu>y> \<prec> Q'" by fact
    hence False by auto
    thus ?case by simp
  next
    case(Input Q' b y)
    have "y \<sharp> (P, a, x, Q)" by fact
    hence yFreshP: "(y::name) \<sharp> P" and yineqx: "y \<noteq> x" and "y \<noteq> a" and "y \<sharp> Q"
      by(simp add: fresh_prod)+
    have "a<x>.Q \<longmapsto>b<y> \<prec> Q'" by fact
    thus ?case using \<open>y \<noteq> a\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close>
    proof(induct rule: inputCases, auto simp add: subject.inject)
      have "\<forall>u. \<exists>P'. a<x>.P \<Longrightarrow>\<^sub>lu in ([(x, y)] \<bullet> P)\<rightarrow>a<y> \<prec> P' \<and> (P', ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel"
      proof(rule allI)
        fix u
        have "a<x>.P \<Longrightarrow>\<^sub>lu in ([(x, y)] \<bullet> P)\<rightarrow>a<y> \<prec> ([(x, y)] \<bullet> P)[y::=u]" (is "?goal")
        proof -
          from yFreshP have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(rule Agent.alphaInput)
          moreover have "a<y>.([(x, y)] \<bullet> P) \<Longrightarrow>\<^sub>lu in ([(x, y)] \<bullet> P)\<rightarrow>a<y> \<prec> ([(x, y)] \<bullet> P)[y::=u]" 
            by(rule Weak_Late_Step_Semantics.Input)
          ultimately show ?goal by(simp add: name_swap)
        qed

        moreover have "(([(x, y)] \<bullet> P)[y::=u], ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel"
        proof -
          from PRelQ have "(P[x::=u], Q[x::=u]) \<in> Rel" by auto
          with \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> show ?thesis by(simp add: renaming)
        qed
        
        ultimately show "\<exists>P'. a<x>.P \<Longrightarrow>\<^sub>lu in ([(x, y)] \<bullet> P)\<rightarrow>a<y> \<prec> P' \<and> (P', ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel" 
          by blast
      qed
      
      thus "\<exists>P''. \<forall>u. \<exists>P'. a<x>.P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<y> \<prec> P' \<and> (P', ([(x, y)] \<bullet> Q)[y::=u]) \<in> Rel" by blast
    qed
  next
    case(Free Q' \<alpha>)
    have "a<x>.Q \<longmapsto>\<alpha> \<prec> Q'" by fact
    hence False by auto
    thus ?case by simp
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

  shows "a{b}.P \<leadsto>\<^sup>^<Rel> a{b}.Q"
proof(induct rule: simCases)
  case(Bound Q' c x)
  have "a{b}.Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
  hence False by auto
  thus ?case by simp
next
  case(Input Q' c x)
  have "a{b}.Q \<longmapsto>c<x> \<prec> Q'" by fact
  hence False by auto
  thus ?case by simp
next
  case(Free Q' \<alpha>)
  have "a{b}.Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  thus "\<exists>P'. a{b}.P \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel" using PRelQ
  proof(induct rule: outputCases, auto simp add: pi.inject residual.inject)
    have "a{b}.P \<Longrightarrow>\<^sub>l\<^sup>^ a[b] \<prec> P" by(rule Output)
    moreover assume "(P, Q') \<in> Rel"
    ultimately show "\<exists>P'. a{b}.P \<Longrightarrow>\<^sub>l\<^sup>^ a[b] \<prec> P' \<and> (P', Q') \<in> Rel" by blast
  qed
qed

lemma matchPres:
  fixes P    :: pi
  and   Q    :: pi
  and   a    :: name
  and   b    :: name
  and   Rel  :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     RelStay: "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> ([a\<frown>a]P, Q) \<in> Rel"
  and     RelRel': "Rel \<subseteq> Rel'"

  shows "[a\<frown>b]P \<leadsto>\<^sup>^<Rel'> [a\<frown>b]Q"
proof(induct rule: simCases)
  case(Bound Q' c x)
  have "x \<sharp> [a\<frown>b]P" by fact
  hence xFreshP: "(x::name) \<sharp> P" by simp
  have "[a\<frown>b]Q \<longmapsto> c<\<nu>x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case cMatch
    have "Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^c<\<nu>x> \<prec> P'"
                                   and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have "[a\<frown>a]P \<Longrightarrow>\<^sub>l\<^sup>^c<\<nu>x> \<prec> P'" by(rule Weak_Late_Semantics.Match)
    with P'RelQ' RelRel' show ?case by blast
  qed
next
  case(Input Q' c x)
  have "x \<sharp> [a\<frown>b]P" by fact
  hence xFreshP: "x \<sharp> P" by simp
  have "[a\<frown>b]Q \<longmapsto>c<x> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case cMatch
    have "Q \<longmapsto> c<x> \<prec> Q'" by fact
    with PSimQ xFreshP obtain P'' where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
      by(force intro: simE)
    have "\<forall>u. \<exists>P'. [a\<frown>a]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
    proof(rule allI)
      fix u
      from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P'" and P'RelQ': "(P', Q'[x::=u]) \<in> Rel"
        by blast
      from PTrans have "[a\<frown>a]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P'" by(rule Weak_Late_Step_Semantics.Match)
      with P'RelQ' RelRel' show "\<exists>P'. [a\<frown>a]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
        by blast
    qed
    thus ?case by blast
  qed
next
  case(Free Q' \<alpha>)
  have "[a\<frown>b]Q \<longmapsto> \<alpha> \<prec> Q'" by fact
  thus ?case
  proof(induct rule: matchCases)
    case cMatch
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans show ?case
    proof(induct rule: transitionCases)
      case Step
      have "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
      hence "[a\<frown>a]P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by(rule Weak_Late_Step_Semantics.Match)
      with PRel RelRel' show ?case by(force simp add: weakTransition_def)
    next
      case Stay
      have "\<alpha> \<prec> P' = \<tau> \<prec> P" by fact
      hence alphaEqTau: "\<alpha> = \<tau>" and PeqP': "P = P'" by(simp add: residual.inject)+
      have "[a\<frown>a]P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> [a\<frown>a]P" by(simp add: weakTransition_def)
      moreover from PeqP' PRel have "([a\<frown>a]P, Q') \<in> Rel" by(blast intro: RelStay)
      ultimately show ?case using RelRel' alphaEqTau by blast
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

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     RelStay: "\<And>P Q a b. \<lbrakk>(P, Q) \<in> Rel; a \<noteq> b\<rbrakk> \<Longrightarrow> ([a\<noteq>b]P, Q) \<in> Rel"
  and     RelRel': "Rel \<subseteq> Rel'"

  shows "[a\<noteq>b]P \<leadsto>\<^sup>^<Rel'> [a\<noteq>b]Q"
proof(cases "a = b")
  assume "a = b"
  thus ?thesis by(auto simp add: weakSimulation_def)
next
  assume aineqb: "a \<noteq> b"
  show ?thesis
  proof(induct rule: simCases)
    case(Bound Q' c x)
    have "x \<sharp> [a\<noteq>b]P" by fact
    hence xFreshP: "(x::name) \<sharp> P" by simp
    have "[a\<noteq>b]Q \<longmapsto> c<\<nu>x> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: mismatchCases)
      case cMismatch
      have "Q \<longmapsto>c<\<nu>x> \<prec> Q'" by fact
      with PSimQ xFreshP obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^c<\<nu>x> \<prec> P'"
        and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans aineqb have "[a\<noteq>b]P \<Longrightarrow>\<^sub>l\<^sup>^c<\<nu>x> \<prec> P'" by(rule Weak_Late_Semantics.Mismatch)
      with P'RelQ' RelRel' show ?case by blast
    qed
  next
    case(Input Q' c x)
    have "x \<sharp> [a\<noteq>b]P" by fact
    hence xFreshP: "x \<sharp> P" by simp
    have "[a\<noteq>b]Q \<longmapsto>c<x> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: mismatchCases)
      case cMismatch
      have "Q \<longmapsto> c<x> \<prec> Q'" by fact
      with PSimQ xFreshP obtain P'' where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
        by(force intro: simE)
      have "\<forall>u. \<exists>P'. [a\<noteq>b]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
      proof(rule allI)
        fix u
        from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P'" and P'RelQ': "(P', Q'[x::=u]) \<in> Rel"
          by blast
        from PTrans aineqb have "[a\<noteq>b]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P'" by(rule Weak_Late_Step_Semantics.Mismatch)
        with P'RelQ' RelRel' show "\<exists>P'. [a\<noteq>b]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>c<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
          by blast
      qed
      thus ?case by blast
    qed
  next
    case(Free Q' \<alpha>)
    have "[a\<noteq>b]Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: mismatchCases)
      case cMismatch
      have "a \<noteq> b" by fact
      have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans show ?case
      proof(induct rule: transitionCases)
        case Step
        have "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
        hence "[a\<noteq>b]P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" using \<open>a \<noteq> b\<close> by(rule Weak_Late_Step_Semantics.Mismatch)
        with PRel RelRel' show ?case by(force simp add: weakTransition_def)
      next
        case Stay
        have "\<alpha> \<prec> P' = \<tau> \<prec> P" by fact
        hence alphaEqTau: "\<alpha> = \<tau>" and PeqP': "P = P'" by(simp add: residual.inject)+
        have "[a\<noteq>b]P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> [a\<noteq>b]P" by(simp add: weakTransition_def)
        moreover from PeqP' PRel aineqb have "([a\<noteq>b]P, Q') \<in> Rel" by(blast intro: RelStay)
        ultimately show ?case using alphaEqTau RelRel' by blast
      qed
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
  
  assumes PSimQ:    "P \<leadsto>\<^sup>^<Rel> Q"
  and     RSimT:    "R \<leadsto>\<^sup>^<Rel'> T"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     RRel'T:   "(R, T) \<in> Rel'"
  and     Par:      "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Rel'\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel''"
  and     Res:      "\<And>P Q a. (P, Q) \<in> Rel'' \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel''"
  and     EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"
  and     EqvtRel'': "eqvt Rel''"

  shows "P \<parallel> R \<leadsto>\<^sup>^<Rel''> Q \<parallel> T"
using \<open>eqvt Rel''\<close>
proof(induct rule: simCasesCont[where C="(P, Q, R, T)"])
  case(Bound Q' a x)
  from \<open>x \<sharp> (P, Q, R, T)\<close> have "x \<sharp> P" and "x \<sharp> R" and "x \<sharp> Q" and "x \<sharp> T" by simp+
  from \<open>Q \<parallel> T \<longmapsto> a<\<nu>x> \<prec> Q'\<close> \<open>x \<sharp> Q\<close> \<open>x \<sharp> T\<close>
  show ?case
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    from PSimQ \<open>Q \<longmapsto> a<\<nu>x> \<prec> Q'\<close> \<open>x \<sharp> P\<close> obtain P' where PTrans:"P \<Longrightarrow>\<^sub>l\<^sup>^ a<\<nu>x> \<prec> P'"
                                                      and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans \<open>x \<sharp> R\<close> have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ a<\<nu>x> \<prec> (P' \<parallel> R)" by(rule Weak_Late_Semantics.Par1B)
    moreover from P'RelQ' RRel'T have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    from RSimT \<open>T \<longmapsto> a<\<nu>x> \<prec> T'\<close> \<open>x \<sharp> R\<close> obtain R' where RTrans:"R \<Longrightarrow>\<^sub>l\<^sup>^ a<\<nu>x> \<prec> R'"
                                                      and R'Rel'T': "(R', T') \<in>  Rel'"
      by(blast dest: simE)
    from RTrans \<open>x \<sharp> P\<close> \<open>x \<sharp> R\<close> have ParTrans: "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ a<\<nu>x> \<prec> (P \<parallel> R')"
      by(blast intro: Weak_Late_Semantics.Par2B)
    moreover from PRelQ R'Rel'T' have "(P \<parallel> R', Q \<parallel>  T') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  qed
next
  case(Input Q' a x)
  from \<open>x \<sharp> (P, Q, R, T)\<close> have "x \<sharp> P" and "x \<sharp> R" and "x \<sharp> Q" and "x \<sharp> T" by simp+
  from \<open>Q \<parallel> T \<longmapsto> a<x> \<prec> Q'\<close> \<open>x \<sharp> Q\<close> \<open>x \<sharp> T\<close>
  show ?case
  proof(induct rule: parCasesB)
    case(cPar1 Q')
    from PSimQ \<open>Q \<longmapsto>a<x> \<prec> Q'\<close> \<open>x \<sharp> P\<close> obtain P''
      where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel" 
      by(blast dest: simE)
    have "\<forall>u. \<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u] \<parallel> T[x::=u]) \<in> Rel''"
    proof(rule allI)
      fix u
      from L1 obtain P' where PTrans:"P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
                          and P'RelQ': "(P', Q'[x::=u]) \<in> Rel" by blast
      from PTrans \<open>x \<sharp> R\<close> have "P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x> \<prec> (P' \<parallel> R)"
        by(rule Weak_Late_Step_Semantics.Par1B)
      moreover from P'RelQ' RRel'T have "(P' \<parallel> R, Q'[x::=u] \<parallel> T) \<in> Rel''" by(rule Par)
      ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x> \<prec> P' \<and>
                            (P', Q'[x::=u] \<parallel> (T[x::=u])) \<in> Rel''" using \<open>x \<sharp> T\<close>
        by(force simp add: forget)
    qed
    thus ?case by force
  next
    case(cPar2 T')
    from RSimT \<open>T \<longmapsto>a<x> \<prec> T'\<close> \<open>x \<sharp> R\<close> obtain R''
      where L1: "\<forall>u. \<exists>R'. R \<Longrightarrow>\<^sub>lu in R''\<rightarrow>a<x> \<prec> R' \<and> (R', T'[x::=u]) \<in> Rel'"
      by(blast dest: simE)
    have "\<forall>u. \<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> P' \<and> (P', Q[x::=u] \<parallel> T'[x::=u]) \<in> Rel''"
    proof(rule allI)
      fix u
      from L1 obtain R' where RTrans:"R \<Longrightarrow>\<^sub>lu in R''\<rightarrow>a<x> \<prec> R'"
                          and R'Rel'T': "(R', T'[x::=u]) \<in>  Rel'" by blast
      from RTrans \<open>x \<sharp> P\<close> have ParTrans: "P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> (P \<parallel> R')"
        by(rule Weak_Late_Step_Semantics.Par2B)
      
      moreover from PRelQ R'Rel'T' have "(P \<parallel> R', Q \<parallel>  T'[x::=u]) \<in> Rel''" by(rule Par)
      
      ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> P' \<and>
                            (P', Q[x::=u] \<parallel> T'[x::=u]) \<in> Rel''" using \<open>x \<sharp> Q\<close>
        by(force simp add: forget)
    qed
    thus ?case by force
  qed
next
  case(Free QT' \<alpha>)
  have "Q \<parallel> T \<longmapsto> \<alpha> \<prec> QT'" by fact
  thus ?case
  proof(induct rule: parCasesF[of _ _ _ _ _ "(P, R)"])
    case(cPar1 Q')
    have "Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> P'" and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from PTrans have Trans: "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> P' \<parallel> R" by(rule Weak_Late_Semantics.Par1F)
    moreover from PRel RRel'T have "(P' \<parallel> R, Q' \<parallel> T) \<in> Rel''" by(blast intro: Par)
    ultimately show ?case by blast
  next
    case(cPar2 T')
    have "T \<longmapsto> \<alpha> \<prec> T'" by fact
    with RSimT obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> R'" and RRel: "(R', T') \<in> Rel'"
      by(blast dest: simE)
    from RTrans have Trans: "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> P \<parallel> R'" by(rule Weak_Late_Semantics.Par2F)
    moreover from PRelQ RRel have "(P \<parallel> R', Q \<parallel> T') \<in> Rel''" by(blast intro: Par)
    ultimately show ?case by blast
  next
    case(cComm1 Q' T' a b x)
    have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" and TTrans: "T \<longmapsto> a[b] \<prec> T'" by fact+
    have "x \<sharp> (P, R)" by fact
    hence xFreshP: "x \<sharp> P" by(simp add: fresh_prod)

    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>lb in P''\<rightarrow>a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q'[x::=b]) \<in> Rel"
      by(blast dest: simE)
      
    from RSimT TTrans obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> R'"
                                  and RRel: "(R', T') \<in> Rel'"
      by(blast dest: simE)
      
    from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec> P' \<parallel> R'" by(rule Weak_Late_Semantics.Comm1)
    moreover from P'RelQ' RRel have "(P' \<parallel> R', Q'[x::=b] \<parallel> T') \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cComm2 Q' T' a b x)
    have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" and TTrans: "T \<longmapsto>a<x> \<prec> T'" by fact+
    have "x \<sharp> (P, R)" by fact
    hence xFreshR: "x \<sharp> R" by(simp add: fresh_prod)
      
    from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'"
                                  and PRel: "(P', Q') \<in> Rel"
      by(blast dest: simE)
    
    from RSimT TTrans xFreshR obtain R' R'' where RTrans: "R \<Longrightarrow>\<^sub>lb in R''\<rightarrow>a<x> \<prec> R'"
                                              and R'Rel'T': "(R', T'[x::=b]) \<in> Rel'"
      by(blast dest: simE)
      
    from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec> P' \<parallel> R'" by(rule Weak_Late_Semantics.Comm2)
    moreover from PRel R'Rel'T' have "(P' \<parallel> R', Q' \<parallel> T'[x::=b]) \<in> Rel''" by(rule Par)
    ultimately show ?case by blast
  next
    case(cClose1 Q' T' a x y)
    have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" and TTrans: "T \<longmapsto>a<\<nu>y> \<prec> T'" by fact+
    have "x \<sharp> (P, R)" and "y \<sharp> (P, R)" by fact+
    hence xFreshP: "x \<sharp> P" and yFreshR: "y \<sharp> R" and yFreshP: "y \<sharp> P" by(simp add: fresh_prod)+
      
    from PSimQ QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>ly in P''\<rightarrow>a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q'[x::=y]) \<in> Rel"
      by(blast dest: simE)
      
    from RSimT TTrans yFreshR obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> R'" 
                                          and R'Rel'T': "(R', T') \<in> Rel'"
      by(blast dest: simE)
      
    from PTrans RTrans yFreshP yFreshR have Trans: "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec> <\<nu>y>(P' \<parallel> R')"
      by(rule Weak_Late_Semantics.Close1)
    moreover from P'RelQ' R'Rel'T' have "(<\<nu>y>(P' \<parallel> R'), <\<nu>y>(Q'[x::=y] \<parallel> T')) \<in> Rel''"
      by(blast intro: Par Res)
    ultimately show ?case by blast
  next
    case(cClose2 Q' T' a x y)
    have QTrans: "Q \<longmapsto>a<\<nu>y> \<prec> Q'" and TTrans: "T \<longmapsto>a<x> \<prec> T'" by fact+
    have "x \<sharp> (P, R)" and "y \<sharp> (P, R)" by fact+
    hence xFreshR: "x \<sharp> R" and yFreshP: "y \<sharp> P" and yFreshR: "y \<sharp> R" by(simp add: fresh_prod)+

    from PSimQ QTrans yFreshP obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> P'"
                                          and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
      
    from RSimT TTrans xFreshR obtain R' R'' where RTrans: "R \<Longrightarrow>\<^sub>ly in R''\<rightarrow>a<x> \<prec> R'"
                                              and R'Rel'T': "(R', T'[x::=y]) \<in> Rel'"
      by(blast dest: simE)
      
    from PTrans RTrans yFreshP yFreshR have Trans: "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> <\<nu>y>(P' \<parallel> R')"
      by(rule Weak_Late_Semantics.Close2)
    moreover from P'RelQ' R'Rel'T' have "(<\<nu>y>(P' \<parallel> R'), <\<nu>y>(Q' \<parallel> T'[x::=y])) \<in> Rel''"
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
  
  assumes PSimQ:    "P \<leadsto>\<^sup>^<Rel> Q"
  and     PRelQ:    "(P, Q) \<in> Rel"
  and     Par:      "\<And>P Q R. (P, Q) \<in> Rel \<Longrightarrow> (P \<parallel> R, Q \<parallel> R) \<in> Rel'"
  and     Res:      "\<And>P Q a. (P, Q) \<in> Rel' \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel'"
  and     EqvtRel:  "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "P \<parallel> R \<leadsto>\<^sup>^<Rel'> Q \<parallel> R"
proof -
  note PSimQ 
  moreover have RSimR: "R \<leadsto>\<^sup>^<Id> R" by(auto intro: reflexive)
  moreover note PRelQ moreover have "(R, R) \<in> Id" by auto
  moreover from Par have "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Id\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel'"
    by auto
  moreover note Res \<open>eqvt Rel\<close>
  moreover have "eqvt Id" by(auto simp add: eqvt_def)
  ultimately show ?thesis using EqvtRel' by(rule parCompose)
qed

lemma resPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   x    :: name
  and   Rel' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     ResRel: "\<And>(P::pi) (Q::pi) (x::name). (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> Rel'"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel: "eqvt Rel"
  and     EqvtRel': "eqvt Rel'"

  shows "<\<nu>x>P \<leadsto>\<^sup>^<Rel'> <\<nu>x>Q"
proof -
  from EqvtRel' show ?thesis
  proof(induct rule: simCasesCont[of _ "(P, Q, x)"])
    case(Bound Q' a y)
    have Trans: "<\<nu>x>Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
    have "y \<sharp> (P, Q, x)" by fact
    hence yineqx: "y \<noteq> x" and yFreshP: "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+
    from Trans \<open>y \<noteq> x\<close> \<open>y \<sharp> Q\<close> show ?case
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      have QTrans: "Q \<longmapsto>a[x] \<prec> Q'" and aineqx: "a \<noteq> x" by fact+

      from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[x] \<prec> P'"
                                    and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)

      have "<\<nu>x>P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> ([(y, x)] \<bullet> P')"
      proof -
        from PTrans aineqx have "<\<nu>x>P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'" by(rule Weak_Late_Semantics.Open)
        moreover from PTrans yFreshP have "y \<sharp> P'" by(force intro: freshTransition)
        ultimately show ?thesis by(simp add: alphaBoundResidual name_swap) 
      qed
      moreover from EqvtRel P'RelQ' RelRel' have "([(y, x)] \<bullet> P', [(y, x)] \<bullet> Q') \<in> Rel'"
        by(blast intro: eqvtRelI)
      ultimately show ?case by blast
    next
      case(cRes Q')
      have QTrans: "Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
      from \<open>x \<sharp> BoundOutputS a\<close> have "x \<noteq> a" by simp

      from PSimQ yFreshP QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> P'"
                                            and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      from PTrans \<open>x \<noteq> a\<close> yineqx yFreshP have ResTrans: "<\<nu>x>P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> (<\<nu>x>P')"
        by(blast intro: Weak_Late_Semantics.ResB)
      moreover from P'RelQ' have "((<\<nu>x>P'), (<\<nu>x>Q')) \<in> Rel'"
        by(rule ResRel)
      ultimately show ?case by blast
    qed
  next
    case(Input Q' a y)
    have "y \<sharp> (P, Q, x)" by fact
    hence yineqx: "y \<noteq> x" and yFreshP: "y \<sharp> P" and "y \<sharp> Q" by(simp add: fresh_prod)+   
    have "<\<nu>x>Q \<longmapsto>a<y> \<prec> Q'" by fact
    thus ?case using yineqx \<open>y \<sharp> Q\<close>
    proof(induct rule: resCasesB)
      case(cOpen a Q')
      thus ?case by simp
    next
      case(cRes Q')
      have QTrans: "Q \<longmapsto>a<y> \<prec> Q'" by fact
      from \<open>x \<sharp> InputS a\<close> have "x \<noteq> a" by simp
      
      from PSimQ QTrans yFreshP obtain P''
        where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<y> \<prec> P' \<and> (P', Q'[y::=u]) \<in> Rel"
        by(blast dest: simE)
      have "\<forall>u. \<exists>P'. <\<nu>x>P \<Longrightarrow>\<^sub>lu in (<\<nu>x>P'')\<rightarrow>a<y> \<prec> P' \<and> (P', (<\<nu>x>Q')[y::=u]) \<in> Rel'"
      proof(rule allI)
        fix u
        show "\<exists>P'. <\<nu>x>P \<Longrightarrow>\<^sub>lu in <\<nu>x>P''\<rightarrow>a<y> \<prec> P' \<and> (P', (<\<nu>x>Q')[y::=u]) \<in> Rel'"
        proof(cases "x=u")
          assume xequ: "x=u"

          have "\<exists>c::name. c \<sharp> (P, P'', Q', x, y, a)" by(blast intro: name_exists_fresh)
          then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP'': "c \<sharp> P''" and cFreshQ': "c \<sharp> Q'"
                                and cineqx: "c \<noteq> x" and cineqy: "c \<noteq> y" and cineqa: "c \<noteq> a"
            by(force simp add: fresh_prod)
        
          from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lc in P''\<rightarrow>a<y> \<prec> P'"
                              and P'RelQ': "(P', Q'[y::=c]) \<in> Rel"
            by blast
          have "<\<nu>x>P \<Longrightarrow>\<^sub>lu in (<\<nu>x>P'')\<rightarrow>a<y> \<prec> <\<nu>c>([(x, c)] \<bullet> P')"
          proof -
            from PTrans yineqx \<open>x \<noteq> a\<close> cineqx have "<\<nu>x>P \<Longrightarrow>\<^sub>lc in (<\<nu>x>P'')\<rightarrow>a<y> \<prec> <\<nu>x>P'"
              by(blast intro: Weak_Late_Step_Semantics.ResB)
            hence "([(x, c)] \<bullet> <\<nu>x>P) \<Longrightarrow>\<^sub>l([(x, c)] \<bullet> c) in ([(x, c)] \<bullet> <\<nu>x>P'')\<rightarrow>([(x, c)] \<bullet> a)<([(x, c)] \<bullet> y)> \<prec> [(x, c)] \<bullet> <\<nu>x>P'"
              by(rule Weak_Late_Step_Semantics.eqvtI)
            moreover from cFreshP have "<\<nu>c>([(x, c)] \<bullet> P) = <\<nu>x>P" by(simp add: alphaRes)
            moreover from cFreshP'' have "<\<nu>c>([(x, c)] \<bullet> P'') = <\<nu>x>P''" by(simp add: alphaRes)
            ultimately show ?thesis using \<open>x \<noteq> a\<close> cineqa yineqx cineqy cineqx xequ by(simp add: name_calc)
          qed
          moreover have "(<\<nu>c>([(x, c)] \<bullet> P'), (<\<nu>x>Q')[y::=u]) \<in> Rel'"
          proof -
            from P'RelQ' have "(<\<nu>x>P', <\<nu>x>(Q'[y::=c])) \<in> Rel'" by(rule ResRel)
            with EqvtRel' have "([(x, c)] \<bullet> <\<nu>x>P', [(x, c)] \<bullet> <\<nu>x>(Q'[y::=c])) \<in> Rel'"  by(rule eqvtRelI)
            with cineqy yineqx cineqx have "(<\<nu>c>([(x, c)] \<bullet> P'), (<\<nu>c>([(x, c)] \<bullet> Q'))[y::=x]) \<in> Rel'"
              by(simp add: name_calc eqvt_subs)
            with cFreshQ' xequ show ?thesis by(simp add: alphaRes)
          qed
          ultimately show ?thesis by blast
        next
          assume xinequ: "x \<noteq> u"
          from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<y> \<prec> P'"
                             and P'RelQ': "(P', Q'[y::=u]) \<in> Rel" by blast
          
          from PTrans \<open>x \<noteq> a\<close> yineqx xinequ have "<\<nu>x>P \<Longrightarrow>\<^sub>lu in (<\<nu>x>P'')\<rightarrow>a<y> \<prec> <\<nu>x>P'"
            by(blast intro: Weak_Late_Step_Semantics.ResB)
          moreover from P'RelQ' xinequ yineqx have "(<\<nu>x>P', (<\<nu>x>Q')[y::=u]) \<in> Rel'"
            by(force intro: ResRel)
          ultimately show ?thesis by blast
        qed
      qed
      thus ?case by blast
    qed
  next
    case(Free Q' \<alpha>)
    have "<\<nu>x>Q \<longmapsto> \<alpha> \<prec> Q'" by fact
    thus ?case
    proof(induct rule: resCasesF)
      case(cRes Q')
      have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^ \<alpha> \<prec> P'"
                             and P'RelQ': "(P', Q') \<in> Rel"
        by(blast dest: simE)
      
      have "<\<nu>x>P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> <\<nu>x>P'"
      proof -
        have xFreshAlpha: "x \<sharp> \<alpha>" by fact
        with PTrans show ?thesis by(rule ResF)
      qed
      moreover from P'RelQ' have "(<\<nu>x>P', <\<nu>x>Q') \<in> Rel'" by(rule ResRel)
      ultimately show ?case by blast
    qed
  qed
qed

lemma resChainI:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   lst :: "name list"

  assumes eqvtRel: "eqvt Rel"
  and     Res:     "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel"
  and     PRelQ:   "P \<leadsto>\<^sup>^<Rel> Q"

  shows "(resChain lst) P \<leadsto>\<^sup>^<Rel> (resChain lst) Q"
proof -
  show ?thesis
  proof(induct lst) (* Base case *)
    from PRelQ show "resChain [] P \<leadsto>\<^sup>^<Rel> resChain [] Q" by simp
  next (* Inductive step *)
    fix a lst
    assume IH: "(resChain lst P) \<leadsto>\<^sup>^<Rel> (resChain lst Q)"
    moreover from Res have "\<And>P Q a. (P, Q) \<in> Rel \<Longrightarrow> (<\<nu>a>P, <\<nu>a>Q) \<in> Rel"
      by simp
    moreover have "Rel \<subseteq> Rel" by simp
    ultimately have "<\<nu>a>(resChain lst P) \<leadsto>\<^sup>^<Rel> <\<nu>a>(resChain lst Q)" using eqvtRel
      by(rule_tac resPres)
    thus "resChain (a # lst) P \<leadsto>\<^sup>^<Rel> resChain (a # lst) Q"
      by simp
  qed
qed

lemma bangPres:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
 
  assumes PSimQ:       "P \<leadsto>\<^sup>^<Rel> Q"
  and     PRelQ:       "(P, Q) \<in> Rel"
  and     Sim:         "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> P \<leadsto>\<^sup>^<Rel> Q"

  and     ParComp:     "\<And>P Q R T. \<lbrakk>(P, Q) \<in> Rel; (R, T) \<in> Rel'\<rbrakk> \<Longrightarrow> (P \<parallel> R, Q \<parallel> T) \<in> Rel'"
  and     Res:         "\<And>P Q x. (P, Q) \<in> Rel' \<Longrightarrow> (<\<nu>x>P, <\<nu>x>Q) \<in> Rel'"

  and     RelStay:        "\<And>P Q. (P \<parallel> !P, Q) \<in> Rel' \<Longrightarrow> (!P, Q) \<in> Rel'"
  and     BangRelRel': "(bangRel Rel) \<subseteq> Rel'"
  and     eqvtRel':    "eqvt Rel'"

  shows "!P \<leadsto>\<^sup>^<Rel'> !Q"
proof -
  have "\<And>Rs P. \<lbrakk>!Q \<longmapsto> Rs; (P, !Q) \<in> bangRel Rel\<rbrakk> \<Longrightarrow> weakSimAct P Rs P Rel'"
  proof -
    fix Rs P
    assume "!Q \<longmapsto> Rs" and "(P, !Q) \<in> bangRel Rel"
    thus "weakSimAct P Rs P Rel'"
    proof(nominal_induct avoiding: P rule: bangInduct)
      case(cPar1B aa x Q')
      have QTrans: "Q \<longmapsto>aa\<guillemotleft>x\<guillemotright> \<prec> Q'" and xFreshQ: "x \<sharp> Q" by fact+
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelT: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        from PRelQ have PSimQ: "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
        from eqvtRel' show ?case
        proof(induct rule: simActBoundCases)
          case(Input a)
          have "aa = InputS a" by fact
          with PSimQ QTrans xFreshP obtain P''
            where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
            by(blast dest: simE)
          have "\<forall>u. \<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x> \<prec> P' \<and> (P', (Q' \<parallel> !Q)[x::=u]) \<in> Rel'"
          proof(rule allI)
            fix u
            from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
                                and P'RelQ': "(P', Q'[x::=u]) \<in> Rel"
              by blast
            
            from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x>\<prec> P' \<parallel> R"
              by(rule Weak_Late_Step_Semantics.Par1B)
            moreover have "(P' \<parallel> R, (Q' \<parallel> !Q)[x::=u]) \<in> Rel'"
            proof -
              from P'RelQ' RBangRelT have "(P' \<parallel> R, Q'[x::=u] \<parallel> !Q) \<in> bangRel Rel"
                by(rule Rel.BRPar)
              with xFreshQ BangRelRel' show ?thesis by(auto simp add: forget)
            qed
            ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P'' \<parallel> R)\<rightarrow>a<x> \<prec> P' \<and>
                                  (P', (Q' \<parallel> !Q)[x::=u]) \<in> Rel'" by blast
          qed
          thus ?case by blast
        next
          case(BoundOutput a)
          have "aa = BoundOutputS a" by fact
          with PSimQ QTrans xFreshP obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
                                                and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)
          from PTrans xFreshR have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x>\<prec> P' \<parallel> R"
            by(rule Weak_Late_Semantics.Par1B)
          moreover from P'RelQ' RBangRelT BangRelRel' have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> Rel'"
            by(blast intro: Rel.BRPar)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cPar1F \<alpha> Q' P)
      have QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from PTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P' \<parallel> R" by(rule Weak_Late_Semantics.Par1F)
          moreover from P'RelQ' RBangRelQ have "(P' \<parallel> R, Q' \<parallel> !Q) \<in> bangRel Rel"
            by(rule Rel.BRPar)
          ultimately show ?case using BangRelRel' by blast
        qed
      qed
    next
      case(cPar2B aa x Q' P)
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (aa\<guillemotleft>x\<guillemotright> \<prec> Q') P Rel'" by fact
      have xFreshQ: "x \<sharp> Q" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" and xFreshR: "x \<sharp> R" by simp+
        from eqvtRel' show ?case
        proof(induct rule: simActBoundCases)
          case(Input a)
          have "aa = InputS a" by fact
          with RBangRelQ IH have "weakSimAct R (a<x> \<prec> Q') R Rel'" by blast
          with xFreshR obtain R'' where L1: "\<forall>u. \<exists>R'. R \<Longrightarrow>\<^sub>lu in R''\<rightarrow>a<x> \<prec> R' \<and> (R', Q'[x::=u]) \<in> Rel'"
            by(force simp add: weakSimAct_def)
          have "\<forall>u. \<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> P' \<and> (P', (Q \<parallel> Q')[x::=u]) \<in> Rel'"
          proof(rule allI)
            fix u
            from L1 obtain R' where RTrans: "R \<Longrightarrow>\<^sub>lu in R''\<rightarrow>a<x> \<prec> R'"
                                and R'Rel'Q': "(R', Q'[x::=u]) \<in> Rel'"
              by blast
            
            from RTrans xFreshP have "P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> P \<parallel> R'"
              by(rule Weak_Late_Step_Semantics.Par2B)
            moreover have "(P \<parallel> R', (Q \<parallel> Q')[x::=u]) \<in> Rel'"
            proof -
              from PRelQ R'Rel'Q' have "(P \<parallel> R', Q \<parallel> Q'[x::=u]) \<in> Rel'"
                by(rule ParComp)
              with xFreshQ show ?thesis by(simp add: forget)
            qed
            ultimately show "\<exists>P'. P \<parallel> R \<Longrightarrow>\<^sub>lu in (P \<parallel> R'')\<rightarrow>a<x> \<prec> P' \<and> (P', (Q \<parallel> Q')[x::=u]) \<in> Rel'"
              by blast
          qed
          thus ?case by blast
        next
          case(BoundOutput a)
          have "aa = BoundOutputS a" by fact
          with IH RBangRelQ have "weakSimAct R (a<\<nu>x> \<prec> Q') R Rel'" by blast
          with xFreshR obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> R'" and R'BangRelQ': "(R', Q') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
          
          from RTrans xFreshP have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P \<parallel> R'"
            by(auto intro: Weak_Late_Semantics.Par2B)
          moreover from PRelQ R'BangRelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'"
            by(rule ParComp)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cPar2F \<alpha> Q' P)
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (\<alpha> \<prec> Q') P Rel'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from RBangRelQ have "weakSimAct R (\<alpha> \<prec> Q') R Rel'" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> R'" and R'RelQ': "(R', Q') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)

          from RTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P \<parallel> R'" by(rule Weak_Late_Semantics.Par2F)
          moreover from PRelQ R'RelQ' have "(P \<parallel> R', Q \<parallel> Q') \<in> Rel'" by(rule ParComp)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cComm1 a x Q' b Q'' P)
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (a[b] \<prec> Q'') P Rel'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" by simp
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
          with QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>lb in P''\<rightarrow>a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q'[x::=b]) \<in> Rel"
            by(blast dest: simE)

          from RBangRelQ have "weakSimAct R (a[b] \<prec> Q'') R Rel'" by(rule IH)
          then obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> R'"
                           and R'RelQ'': "(R', Q'') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
        
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Late_Semantics.Comm1)
          moreover from P'RelQ' R'RelQ'' have "(P' \<parallel> R', Q'[x::=b] \<parallel> Q'') \<in> Rel'"
            by(rule ParComp)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cComm2 a b Q' x Q'' P)
      have QTrans: "Q \<longmapsto>a[b] \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (a<x> \<prec> Q'') P Rel'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshR: "x \<sharp> R" by simp
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
          with QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from RBangRelQ have "weakSimAct R (a<x> \<prec> Q'') R Rel'" by(rule IH)
          with xFreshR obtain R' R'' where RTrans: "R \<Longrightarrow>\<^sub>lb in R''\<rightarrow>a<x> \<prec> R'"
                                       and R'BangRelQ'': "(R', Q''[x::=b]) \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
        
          from PTrans RTrans have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> (P' \<parallel> R')"
            by(rule Weak_Late_Semantics.Comm2)
          moreover from P'RelQ' R'BangRelQ'' have "(P' \<parallel> R', Q' \<parallel> Q''[x::=b]) \<in> Rel'"
            by(rule ParComp)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cClose1 a x Q' y Q'' P)
      have QTrans: "Q \<longmapsto> a<x> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (a<\<nu>y> \<prec> Q'') P Rel'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" and "y \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshP: "x \<sharp> P" by simp
        have "y \<sharp> P \<parallel> R" by fact
        hence yFreshR: "y \<sharp> R" and yFreshP: "y \<sharp> P" by simp+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
          with QTrans xFreshP obtain P' P'' where PTrans: "P \<Longrightarrow>\<^sub>ly in P''\<rightarrow>a<x> \<prec> P'"
                                              and P'RelQ': "(P', Q'[x::=y]) \<in> Rel"
            by(blast dest: simE)
          
          from RBangRelQ have "weakSimAct R (a<\<nu>y> \<prec> Q'') R Rel'" by(rule IH)
          with yFreshR obtain R' where RTrans: "R \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> R'"
                                   and R'RelQ'': "(R', Q'') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
        
          from PTrans RTrans yFreshP yFreshR have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> <\<nu>y>(P' \<parallel> R')"
            by(rule Weak_Late_Semantics.Close1)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>y>(P' \<parallel> R'), <\<nu>y>(Q'[x::=y] \<parallel> Q'')) \<in> Rel'"
            by(force intro: ParComp Res)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cClose2 a y Q' x Q'' P)
      have QTrans: "Q \<longmapsto> a<\<nu>y> \<prec> Q'" by fact
      have IH: "\<And>P. (P, !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P (a<x> \<prec> Q'') P Rel'" by fact
      have "(P, Q \<parallel> !Q) \<in> bangRel Rel" and "x \<sharp> P" and "y \<sharp> P" by fact+
      thus ?case
      proof(induct rule: BRParCases)
        case(BRPar P R)
        have PRelQ: "(P, Q) \<in> Rel" and RBangRelQ: "(R, !Q) \<in> bangRel Rel" by fact+
        have "x \<sharp> P \<parallel> R" by fact
        hence xFreshR: "x \<sharp> R" by simp
        have "y \<sharp> P \<parallel> R" by fact
        hence yFreshP: "y \<sharp> P" and yFreshR: "y \<sharp> R" by simp+
        show ?case
        proof(induct rule: simActFreeCases)
          case Der
          from PRelQ have "P \<leadsto>\<^sup>^<Rel> Q" by(rule Sim)
          with QTrans yFreshP obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> P'"
                                          and P'RelQ': "(P', Q') \<in> Rel"
            by(blast dest: simE)

          from RBangRelQ have "weakSimAct R (a<x> \<prec> Q'') R Rel'" by(rule IH)
          with xFreshR obtain R' R'' where RTrans: "R \<Longrightarrow>\<^sub>ly in R''\<rightarrow>a<x> \<prec> R'"
                                       and R'RelQ'': "(R', Q''[x::=y]) \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
        
          from PTrans RTrans yFreshP yFreshR have "P \<parallel> R \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> <\<nu>y>(P' \<parallel> R')"
            by(rule Weak_Late_Semantics.Close2)
          moreover from P'RelQ' R'RelQ'' have "(<\<nu>y>(P' \<parallel> R'), <\<nu>y>(Q' \<parallel> Q''[x::=y])) \<in> Rel'"
            by(force intro: ParComp Res)
          ultimately show ?case by blast
        qed
      qed
    next
      case(cBang Rs)
      have IH: "\<And>P. (P, Q \<parallel> !Q) \<in> bangRel Rel \<Longrightarrow> weakSimAct P Rs P Rel'" by fact
      have "(P, !Q) \<in> bangRel Rel" by fact
      thus ?case
      proof(induct rule: BRBangCases)
        case(BRBang P)
        have PRelQ: "(P, Q) \<in> Rel" by fact
        hence "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
        with PRelQ have "(P \<parallel> !P, Q \<parallel> !Q) \<in> bangRel Rel" by(rule Rel.BRPar)
        hence "weakSimAct (P \<parallel> !P) Rs (P \<parallel> !P) Rel'" by(rule IH)
        thus ?case
        proof(simp (no_asm) add: weakSimAct_def, auto)
          fix Q' a x
          assume "weakSimAct (P \<parallel> !P) (a<\<nu>x> \<prec> Q') (P \<parallel> !P) Rel'" and "x \<sharp> P"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
          from PTrans have "!P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
            by(force intro: Weak_Late_Step_Semantics.Bang simp add: weakTransition_def)
          with P'RelQ' show "\<exists>P'. !P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel'" by blast
        next
          fix Q' a x
          assume "weakSimAct (P \<parallel> !P) (a<x> \<prec> Q') (P \<parallel> !P) Rel'" and "x \<sharp> P"
          then obtain P'' where L1: "\<forall>u. \<exists>P'. P \<parallel> !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
          have "\<forall>u. \<exists>P'. !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'"
          proof(rule allI)
            fix u
            from L1 obtain P' where PTrans: "P \<parallel> !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
                                and P'RelQ': "(P', Q'[x::=u]) \<in> Rel'"
              by blast
            from PTrans have "!P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'" by(rule Weak_Late_Step_Semantics.Bang)
            with P'RelQ' show "\<exists>P'. !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'" by blast
          qed
          thus "\<exists>P''. \<forall>u. \<exists>P'. !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel'" by blast
        next
          fix Q' \<alpha>
          assume "weakSimAct (P \<parallel> !P) (\<alpha> \<prec> Q') (P \<parallel> !P) Rel'"
          then obtain P' where PTrans: "(P \<parallel> !P) \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
                           and P'RelQ': "(P', Q') \<in> Rel'"
            by(simp add: weakSimAct_def, blast)
          from PTrans show "\<exists>P'. !P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel'"
          proof(induct rule: transitionCases)
            case Step
            have "P \<parallel> !P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
            hence "!P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by(rule Weak_Late_Step_Semantics.Bang)
            with P'RelQ' show ?case by(force simp add: weakTransition_def)
          next
            case Stay
            have "\<alpha> \<prec> P' = \<tau> \<prec> P \<parallel> !P" by fact
            hence \<alpha>eq\<tau>: "\<alpha> = \<tau>" and P'eqP: "P' = P \<parallel> !P" by(simp add: residual.inject)+
            have "!P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> !P" by(simp add: weakTransition_def)
            moreover from P'eqP P'RelQ' have "(!P, Q') \<in> Rel'" by(blast intro: RelStay)
            ultimately show ?case using \<alpha>eq\<tau> by blast
          qed
        qed
      qed
    qed
  qed
  moreover from PRelQ have "(!P, !Q) \<in> bangRel Rel" by(rule Rel.BRBang)
  ultimately show ?thesis by(simp add: simDef)
qed

end
