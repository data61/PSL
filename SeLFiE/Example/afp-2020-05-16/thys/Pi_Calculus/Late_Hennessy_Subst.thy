(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Late_Hennessy_Subst
  imports Weak_Late_Bisim_Subst Weak_Late_Cong_Subst
begin

lemma sim1:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  
  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"

  shows "\<tau>.(P) \<leadsto><Rel> Q"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  moreover have xFreshP: "x \<sharp> P"
  proof -
    have "x \<sharp> \<tau>.(P)" by fact
    thus ?thesis by simp
  qed
  ultimately obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Sim.simE)
  from PTrans have "\<tau>.(P) \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  proof(induct rule: transitionCases)
    case Step
    have "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'" by fact
    with xFreshP obtain P''' P'' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                   and P'''Trans:  "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                   and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
    proof -
      have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule Late_Semantics.Tau)
      thus ?thesis using PChain by auto
    qed
    thus ?case using P'''Trans P''Chain by(blast intro: Weak_Late_Step_Semantics.transitionI)
  next
    case Stay
    have "a<\<nu>x> \<prec> P' = \<tau> \<prec> P" by fact
    hence False by(simp add: residual.inject)
    thus ?case by simp
  qed
  with P'RelQ' show ?case by blast
next
  case(Input Q' a x)
  have "Q \<longmapsto>a<x> \<prec> Q'" by fact
  moreover have xFreshP: "x \<sharp> P"
  proof -
    have "x \<sharp> \<tau>.(P)" by fact
    thus ?thesis by simp
  qed
  ultimately obtain P'' where L1: "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Sim.simE)
  have "\<And>u. \<exists>P'. \<tau>.(P) \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
  proof -
    fix u
    from L1 obtain P' where PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'" and P'RelQ': "(P', Q'[x::=u]) \<in> Rel" by blast    
    from PTrans xFreshP obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                     and P'''Trans:  "P''' \<longmapsto>a<x> \<prec> P''"
                                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
    proof -
      have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule Late_Semantics.Tau)
      thus ?thesis using PChain by auto
    qed
    hence "\<tau>.(P) \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'" using P'''Trans P''Chain by(blast intro: Weak_Late_Step_Semantics.transitionI)
    with P'RelQ' show "\<exists>P'. \<tau>.(P) \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel" by blast
  qed
  thus ?case by blast
next
  case(Free Q' \<alpha>)
  have Trans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  then obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" using PSimQ
    by(blast dest: Weak_Late_Sim.simE)
  from PTrans have "\<tau>.(P) \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
  proof(induct rule: transitionCases)
    case Step
    have "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
    then obtain P''' P'' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                           and P'''Trans:  "P''' \<longmapsto>\<alpha> \<prec> P''"
                           and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
    proof -
      have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule Late_Semantics.Tau)
      thus ?thesis using PChain by auto
    qed
    thus ?case using P'''Trans P''Chain by(blast intro: Weak_Late_Step_Semantics.transitionI)
  next
    case Stay
    have "\<alpha> \<prec> P' = \<tau> \<prec> P" by fact
    hence "\<alpha> = \<tau>" and "P = P'" by(simp add: residual.inject)+
    moreover have "\<tau>.(P) \<Longrightarrow>\<^sub>l\<tau> \<prec> P"
    proof -
      have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau>\<tau>.(P)" by simp
      moreover have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule Late_Semantics.Tau)
      moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
      ultimately show ?thesis by(blast intro: Weak_Late_Step_Semantics.transitionI)
    qed
    ultimately show ?case by force
  qed
  with P'RelQ' show ?case by blast
qed

lemma sim2:
  fixes P  :: pi
  and   Q  :: pi
  and   P' :: pi

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     PRelQ: "(P, Q) \<in> Rel"
  and     PTrans: "P \<longmapsto>\<tau> \<prec> P'"
  and     P'RelP: "(P', P) \<in> Rel"
  and     Trans: "\<And>P Q R. \<lbrakk>(P, Q) \<in> Rel; (Q, R) \<in> Rel\<rbrakk> \<Longrightarrow> (P, R) \<in> Rel"

  shows "P \<leadsto><Rel> \<tau>.(Q)"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "\<tau>.(Q) \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  hence False by(force intro: tauCases)
  thus ?case by simp
next
  case(Input Q' a x)
  have "\<tau>.(Q) \<longmapsto> a<x> \<prec> Q'" by fact
  hence False by(force intro: tauCases)
  thus ?case by simp
next
  case(Free Q' \<alpha>)

  have "\<tau>.(Q) \<longmapsto>\<alpha> \<prec> Q'" by fact
  hence "\<alpha> = \<tau>" and "Q = Q'" by(drule_tac tauCases, auto simp add: pi.inject residual.inject)+
  moreover from PTrans have "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'" by(rule Weak_Late_Step_Semantics.singleActionChain)
  moreover from P'RelP PRelQ have "(P', Q) \<in> Rel" by(rule Trans)
  ultimately show ?case by blast
qed
  

lemma sim3:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     PRelQ: "(P, Q) \<in> Rel"
  and     L1: "\<And>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> (Q', Q) \<notin> Rel"
  and     Trans: "\<And>P Q R. \<lbrakk>(P, Q) \<in> Rel; (Q, R) \<in> Rel\<rbrakk> \<Longrightarrow> (P, R) \<in> Rel"
  and     Sym: "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> (Q, P) \<in> Rel"

  shows "P \<leadsto><Rel> Q"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and "x \<sharp> P" by fact+
  with PSimQ obtain P' where "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'" and "(P', Q') \<in> Rel" by(blast dest: Weak_Late_Sim.simE)
  thus ?case by(auto simp add: weakTransition_def)
next
  case(Input Q' a x)
  have "Q \<longmapsto>a<x> \<prec> Q'" and "x \<sharp> P" by fact+
  with PSimQ show ?case by(auto dest: Weak_Late_Sim.simE)
next
  case(Free Q' \<alpha>)
  have QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: Weak_Late_Sim.simE)
  from PTrans show ?case
  proof(induct rule: transitionCases)
    case Step
    have "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
    with P'RelQ' show ?case by blast
  next
    case Stay
    have "\<alpha> \<prec> P' = \<tau> \<prec> P" by fact
    hence \<alpha>eq\<tau>: "\<alpha> = \<tau>" and PeqP': "P = P'" by(simp add: residual.inject)+
    from PRelQ P'RelQ' PeqP' Trans Sym have "(Q, Q') \<in> Rel" by blast
    moreover from QTrans \<alpha>eq\<tau> have "(Q', Q) \<notin> Rel" by(blast dest: L1)
    ultimately have False by(blast intro: Sym)
    thus ?case by simp
  qed
qed

lemma hennessy:
  fixes P :: pi
  and   Q :: pi

  assumes PBisimQ: "P \<approx>\<^sup>s Q"

  shows "(\<tau>.(P) \<simeq>\<^sup>s Q) \<or> (P \<simeq>\<^sup>s Q) \<or> (P \<simeq>\<^sup>s (\<tau>.(Q)))"
proof(case_tac "\<exists>P'. P \<longmapsto>\<tau> \<prec> P' \<and> P' \<approx> P")
  assume "\<exists>P'. P \<longmapsto> \<tau> \<prec> P' \<and> P' \<approx> P"
  then obtain P' where PTrans: "P \<longmapsto>\<tau> \<prec> P'" and P'BisimP: "P' \<approx> P" by blast

  have "P \<simeq>\<^sup>s \<tau>.(Q)"
  proof(rule_tac Weak_Late_Cong_Subst.unfoldI, auto)
    fix s
    from PBisimQ have "P[<s>] \<leadsto>\<^sup>^<weakBisim> Q[<s>]" by(force simp add: substClosed_def dest: Weak_Late_Bisim.unfoldE)
    moreover from PBisimQ have "P[<s>] \<approx> Q[<s>]" by(simp add: substClosed_def)
    thus "P[<s>]\<leadsto><weakBisim> \<tau>.(Q[<s>])" using PTrans P'BisimP Weak_Late_Bisim.transitive by(rule sim2)
    
  have "P \<leadsto><weakBisim> \<tau>.(Q)"
  proof -
  qed
  moreover have "\<tau>.(Q) \<leadsto><weakBisim> P"
  proof -
    from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
    thus ?thesis by(rule sim1)
  qed
  ultimately have "" by(simp add: congruence_def)
  thus ?thesis by simp
next
  assume "\<not>(\<exists>P'. P \<longmapsto>\<tau> \<prec> P' \<and> P' \<approx> P)"
  hence L1: "\<And>P'. P\<longmapsto>\<tau> \<prec> P' \<Longrightarrow> \<not>(P' \<approx> P)" by simp
  show ?thesis
  proof(case_tac "\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> Q")
    assume "\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> Q"
    then obtain Q' where QTrans: "Q \<longmapsto>\<tau> \<prec> Q'" and Q'BisimQ: "Q' \<approx> Q" by blast
    have "\<tau>.(P) \<leadsto><weakBisim> Q"
    proof -
      from PBisimQ have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis by(rule sim1)
    qed
    moreover have "Q \<leadsto><weakBisim> \<tau>.(P)"
    proof -
      from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
      moreover from PBisimQ have "Q \<approx> P" by(rule Weak_Late_Bisim.symetric)
      ultimately show ?thesis using QTrans Q'BisimQ Weak_Late_Bisim.transitive by(rule sim2)
    qed
    ultimately have "\<tau>.(P) \<simeq> Q" by(simp add: congruence_def)
    thus ?thesis by simp
  next
    assume "\<not>(\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> Q)"
    hence L2: "\<And>Q'. Q\<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<not>(Q' \<approx> Q)" by simp

    have "P \<leadsto><weakBisim> Q"
    proof -
      from PBisimQ have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis using PBisimQ L2 Weak_Late_Bisim.transitive Weak_Late_Bisim.symetric by(rule sim3)
    qed
    moreover have "Q \<leadsto><weakBisim> P"
    proof -
      from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
      moreover from PBisimQ have "Q \<approx> P" by(rule Weak_Late_Bisim.symetric)
      ultimately show ?thesis using L1 Weak_Late_Bisim.transitive Weak_Late_Bisim.symetric by(rule sim3)
    qed
    ultimately have "P \<simeq> Q" by(simp add: congruence_def)
    thus ?thesis by simp
  qed
qed
