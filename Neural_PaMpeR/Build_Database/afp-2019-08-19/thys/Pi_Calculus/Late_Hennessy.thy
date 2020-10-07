(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Late_Hennessy
  imports Weak_Late_Bisim Weak_Late_Cong
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
  and     PTrans: "P \<longmapsto>\<tau> \<prec> P'"
  and     P'RelQ: "(P', Q) \<in> Rel"

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
  ultimately show ?case using P'RelQ by blast
qed
  

lemma sim3:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<^sup>^<Rel> Q"
  and     L1: "\<And>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> (P, Q') \<notin> Rel"

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
    from P'RelQ' PeqP' have "(P, Q') \<in> Rel" by blast
    moreover from QTrans \<alpha>eq\<tau> have "(P, Q') \<notin> Rel" by(blast dest: L1)
    ultimately have False by  simp
    thus ?case by simp
  qed
qed

lemma hennessyLeft:
  fixes P :: pi
  and   Q :: pi

  assumes PBisimQ: "P \<approx> Q"

  shows "\<tau>.(P) \<simeq> Q \<or> P \<simeq> Q \<or> P \<simeq> \<tau>.(Q)"
proof(case_tac "\<exists>P'. P \<longmapsto>\<tau> \<prec> P' \<and> P' \<approx> Q")
  assume "\<exists>P'. P \<longmapsto> \<tau> \<prec> P' \<and> P' \<approx> Q"
  then obtain P' where PTrans: "P \<longmapsto>\<tau> \<prec> P'" and P'BisimP: "P' \<approx> Q" by blast

  have "P \<leadsto><weakBisim> \<tau>.(Q)"
  proof -
    from PBisimQ have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: Weak_Late_Bisim.unfoldE)
    thus ?thesis using PTrans P'BisimP by(rule sim2)
  qed
  moreover have "\<tau>.(Q) \<leadsto><weakBisim> P"
  proof -
    from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
    thus ?thesis by(rule sim1)
  qed
  ultimately have "P \<simeq> \<tau>.(Q)" by(simp add: congruence_def)
  thus ?thesis by simp
next
  assume "\<not>(\<exists>P'. P \<longmapsto>\<tau> \<prec> P' \<and> P' \<approx> Q)"
  hence L1: "\<And>P'. P\<longmapsto>\<tau> \<prec> P' \<Longrightarrow> \<not>(Q \<approx> P')" by(auto intro: Weak_Late_Bisim.symmetric)
  show ?thesis
  proof(case_tac "\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> P")
    assume "\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> P"
    then obtain Q' where QTrans: "Q \<longmapsto>\<tau> \<prec> Q'" and Q'BisimP: "Q' \<approx> P" by blast
    have "\<tau>.(P) \<leadsto><weakBisim> Q"
    proof -
      from PBisimQ have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis by(rule sim1)
    qed
    moreover have "Q \<leadsto><weakBisim> \<tau>.(P)"
    proof -
      from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis using QTrans Q'BisimP by(rule sim2)
    qed
    ultimately have "\<tau>.(P) \<simeq> Q" by(simp add: congruence_def)
    thus ?thesis by simp
  next
    assume "\<not>(\<exists>Q'. Q \<longmapsto>\<tau> \<prec> Q' \<and> Q' \<approx> P)"
    hence L2: "\<And>Q'. Q\<longmapsto>\<tau> \<prec> Q' \<Longrightarrow> \<not>(P \<approx> Q')" by(auto intro: Weak_Late_Bisim.symmetric)

    have "P \<leadsto><weakBisim> Q"
    proof -
      from PBisimQ have "P \<leadsto>\<^sup>^<weakBisim> Q" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis using L2 by(rule sim3)
    qed
    moreover have "Q \<leadsto><weakBisim> P"
    proof -
      from PBisimQ have "Q \<leadsto>\<^sup>^<weakBisim> P" by(blast dest: Weak_Late_Bisim.unfoldE)
      thus ?thesis using L1 by(rule sim3)
    qed
    ultimately have "P \<simeq> Q" by(simp add: congruence_def)
    thus ?thesis by simp
  qed
qed

lemma boundOutputRemoveTau:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "\<tau>.(P) \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  and     "x \<sharp> P"

  shows "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
proof -
  from assms obtain P''' P'''' where PChain:"\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
                                 and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''''"
                                 and P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: Weak_Late_Step_Semantics.transitionE)
  show ?thesis
  proof(case_tac "P''' = \<tau>.(P)")
    assume "P''' = \<tau>.(P)"
    with P'''Trans have False by auto
    thus ?thesis by simp
  next
    assume "P''' \<noteq> \<tau>.(P)"
    with PChain obtain P'' where PTrans: "\<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'''"
      by (auto elim: converse_rtranclE)
    from PTrans have "P = P''"
      by(force elim: tauCases simp add: pi.inject residual.inject)
    with P''Chain P'''Trans P''''Chain show ?thesis
      by(blast intro: Weak_Late_Step_Semantics.transitionI)
  qed
qed      

lemma inputRemoveTau:
  fixes P     :: pi
  and   u     :: name
  and   P'''' :: pi
  and   a     :: name  
  and   x     :: name
  and   P'    :: pi

  assumes "\<tau>.(P) \<Longrightarrow>\<^sub>lu in P'''' \<rightarrow> a<x> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>lu in P'''' \<rightarrow> a<x> \<prec> P'"
proof -
  from assms obtain P''' where PChain:"\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''''"
                            and P''''Chain: "P''''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: Weak_Late_Step_Semantics.transitionE)
  show ?thesis
  proof(case_tac "P''' = \<tau>.(P)")
    assume "P''' = \<tau>.(P)"
    with P'''Trans have False by auto
    thus ?thesis by simp
  next
    assume "P''' \<noteq> \<tau>.(P)"
    with PChain obtain P'' where PTrans: "\<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'''"
      by (auto elim: converse_rtranclE)
    from PTrans have "P = P''"
      by(force elim: tauCases simp add: pi.inject residual.inject)
    with P''Chain P'''Trans P''''Chain show ?thesis
      by(blast intro: Weak_Late_Step_Semantics.transitionI)
  qed
qed      

lemma outputRemoveTau:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "\<tau>.(P) \<Longrightarrow>\<^sub>la[b] \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>la[b] \<prec> P'"
proof -
  from assms obtain P''' P'''' where PChain:"\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
                                 and P'''Trans: "P''' \<longmapsto>a[b] \<prec> P''''"
                                 and P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: Weak_Late_Step_Semantics.transitionE)
  show ?thesis
  proof(case_tac "P''' = \<tau>.(P)")
    assume "P''' = \<tau>.(P)"
    with P'''Trans have False by auto
    thus ?thesis by simp
  next
    assume "P''' \<noteq> \<tau>.(P)"
    with PChain obtain P'' where PTrans: "\<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'''"
      by (auto elim: converse_rtranclE)
    from PTrans have "P = P''"
      by(force elim: tauCases simp add: pi.inject residual.inject)
    with P''Chain P'''Trans P''''Chain show ?thesis
      by(blast intro: Weak_Late_Step_Semantics.transitionI)
  qed
qed      

lemma tauRemoveTau:
  fixes P  :: pi
  and   P' :: pi

  assumes PTrans: "\<tau>.(P) \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
  and     PineqP': "P \<noteq> P'"

  shows "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
proof -
  from PTrans obtain P''' P'''' where PChain:"\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> P'''"
                                  and P'''Trans: "P''' \<longmapsto>\<tau> \<prec> P''''"
                                  and P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: Weak_Late_Step_Semantics.transitionE)
  show ?thesis
  proof(case_tac "P''' = \<tau>.(P)")
    assume "P''' = \<tau>.(P)"
    with P'''Trans have "P = P''''"
      by(force elim: tauCases simp add: pi.inject residual.inject)
    with P''''Chain PineqP' obtain P'' where PTrans: "P \<longmapsto>\<tau> \<prec> P''" and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
      by (auto elim: converse_rtranclE)
    moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
    ultimately show ?thesis by(rule_tac Weak_Late_Step_Semantics.transitionI)
  next
    assume "P''' \<noteq> \<tau>.(P)"
    with PChain obtain P'' where PTrans: "\<tau>.(P) \<longmapsto>\<tau> \<prec> P''" and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'''"
      by (auto elim: converse_rtranclE)
    from PTrans have "P = P''"
      by(force elim: tauCases simp add: pi.inject residual.inject)
    with P''Chain P'''Trans P''''Chain show ?thesis
      by(blast intro: Weak_Late_Step_Semantics.transitionI)
  qed
qed      

lemma sim4:
  fixes P :: pi
  and   Q :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "\<tau>.(P) \<leadsto><Rel> Q"

  shows "P \<leadsto>\<^sup>^<Rel> Q"
proof(induct rule: Weak_Late_Sim.simCases)
  case(Bound Q' a x)
  have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and xFreshP: "x \<sharp> P" by fact+

  with PSimQ obtain P' where PTrans: "\<tau>.(P) \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
                         and P'RelQ': "(P', Q') \<in> Rel" by(auto dest: simE)
  from PTrans xFreshP have "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'" 
    by(blast intro: boundOutputRemoveTau)
  hence "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'" by(simp add: weakTransition_def)
  with P'RelQ' show ?case by blast
next
  case(Input Q' a x)
  have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" and xFreshP: "x \<sharp> P" by fact+
  with PSimQ obtain P'' where PSim: "\<forall>u. \<exists>P'. \<tau>.(P) \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
    by(auto dest: simE)
  have "\<forall>u. \<exists>P'. P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"
  proof(rule allI)
    fix u
    from PSim obtain P' where PTrans: "\<tau>.(P) \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'" and P'RelQ': "(P', Q'[x::=u]) \<in> Rel"
      by blast
    with PTrans have "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P'" by(blast intro: inputRemoveTau)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow> a<x> \<prec> P' \<and> (P', Q'[x::=u]) \<in> Rel"  by blast
  qed
  thus ?case by blast
next
  case(Free Q' \<alpha>)
  with PSimQ obtain P' where PTrans: "\<tau>.(P) \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
                         and P'RelQ': "(P', Q') \<in> Rel" by(auto dest: simE)
  from PTrans show ?case
  proof(cases \<alpha>, auto)
    fix a b
    assume "\<tau>.(P) \<Longrightarrow>\<^sub>l(a::name)[b] \<prec> P'"
    hence "P \<Longrightarrow>\<^sub>la[b] \<prec> P'" by(rule outputRemoveTau)
    hence "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'" by(simp add: weakTransition_def)
    with P'RelQ' show "\<exists>P'. P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P' \<and> (P', Q') \<in> Rel" by blast
  next
    assume PTrans: "\<tau>.(P) \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
    thus "\<exists>P'. P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P' \<and> (P', Q') \<in> Rel"
    proof(case_tac "P = P'")
      assume "P = P'"
      hence "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P'" by(simp add: weakTransition_def)
      with P'RelQ' show ?thesis by blast
    next
      assume "P \<noteq> P'"
      hence "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'" using PTrans by(rule_tac tauRemoveTau)
      hence "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P'" by(simp add: weakTransition_def)
      with P'RelQ' show ?thesis by blast
    qed
  qed
qed

lemma sim5:
  fixes P :: pi
  and   Q :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto><Rel> \<tau>.(Q)"
  and     L1: "\<And>P Q. (P, Q) \<in> Rel \<Longrightarrow> P \<leadsto>\<^sup>^<Rel> Q"

  shows "P \<leadsto>\<^sup>^<Rel> Q"
proof -
  have "\<tau>.(Q) \<longmapsto>\<tau> \<prec> Q" by(rule Late_Semantics.Tau)
  with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'" and P'RelQ: "(P', Q) \<in> Rel"
    by(auto dest: simE)
  from PTrans have PChain:"P \<Longrightarrow>\<^sub>\<tau> P'" by(rule Weak_Late_Step_Semantics.tauTransitionChain)
  from P'RelQ have P'SimQ: "P' \<leadsto>\<^sup>^<Rel> Q" by(rule L1)
  show ?thesis
  proof(induct rule: Weak_Late_Sim.simCases)
    case(Bound Q' a x)
    have QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and xFreshP: "x \<sharp> P" by fact+
    from PChain xFreshP have xFreshP': "x \<sharp> P'" by(rule freshChain)

    with P'SimQ QTrans obtain P'' where P''Trans: "P' \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P''"
                                    and P''RelQ': "(P'', Q') \<in> Rel" by(auto dest: Weak_Late_Sim.simE)
    from PChain P''Trans have "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P''" 
      by(rule chainTransitionAppend)
    with P''RelQ' show ?case by blast
  next
    case(Input Q' a x)
    have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" and xFreshP: "x \<sharp> P" by fact+
    from PChain xFreshP have xFreshP': "x \<sharp> P'" by(rule freshChain)
    with P'SimQ QTrans obtain P''' where PSim: "\<forall>u. \<exists>P''. P' \<Longrightarrow>\<^sub>lu in P''' \<rightarrow> a<x> \<prec> P'' \<and> (P'', Q'[x::=u]) \<in> Rel"
      by(auto dest: Weak_Late_Sim.simE)
    have "\<forall>u. \<exists>P''. P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'' \<and> (P'', Q'[x::=u]) \<in> Rel"
    proof(rule allI)
      fix u
      from PSim obtain P'' where P'Trans: "P' \<Longrightarrow>\<^sub>lu in P''' \<rightarrow> a<x> \<prec> P''" and P''RelQ': "(P'', Q'[x::=u]) \<in> Rel"
        by blast
      from PChain P'Trans have "P \<Longrightarrow>\<^sub>lu in P''' \<rightarrow>a<x> \<prec> P''" by(rule Weak_Late_Step_Semantics.chainTransitionAppend)
      with P''RelQ' show "\<exists>P''. P \<Longrightarrow>\<^sub>lu in P''' \<rightarrow> a<x> \<prec> P'' \<and> (P'', Q'[x::=u]) \<in> Rel"  by blast
    qed
    thus ?case by blast
  next
    case(Free Q' \<alpha>)
    with P'SimQ obtain P'' where P'Trans: "P' \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P''"
                             and P''RelQ': "(P'', Q') \<in> Rel" by(auto dest: Weak_Late_Sim.simE)
    from PChain P'Trans have "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P''" by(rule chainTransitionAppend)
    with P''RelQ' show ?case by blast
  qed
qed

lemma hennessyRight:
  fixes P :: pi
  and   Q :: pi

  assumes "\<tau>.(P) \<simeq> Q \<or> P \<simeq> Q \<or> P \<simeq> \<tau>.(Q)"

  shows "P \<approx> Q"
using assms
proof(rule disjE)
  assume PeqQ: "\<tau>.(P) \<simeq> Q"
  have "P \<leadsto>\<^sup>^<weakBisim> Q"
  proof -
    from PeqQ have "\<tau>.(P) \<leadsto><weakBisim> Q" by(simp add: congruence_def)
    thus ?thesis by(rule sim4)
  qed
  moreover have "Q \<leadsto>\<^sup>^<weakBisim> P"
  proof -
    from PeqQ have "Q \<leadsto><weakBisim> \<tau>.(P)" by(simp add: congruence_def)
    thus ?thesis using Weak_Late_Bisim.unfoldE(1) by(rule sim5)
  qed
  ultimately show ?thesis by(blast intro: Weak_Late_Bisim.unfoldI)
next
  assume "P \<simeq> Q \<or> P \<simeq> \<tau>.(Q)"
  thus ?thesis
  proof(rule disjE)
    assume "P \<simeq> Q"
    thus ?thesis by(rule congruenceWeakBisim)
  next
    assume PeqQ: "P \<simeq> \<tau>.(Q)"
    have "P \<leadsto>\<^sup>^<weakBisim> Q"
    proof -
      from PeqQ have "P \<leadsto><weakBisim> \<tau>.(Q)" by(simp add: congruence_def)
      thus ?thesis using Weak_Late_Bisim.unfoldE(1) by(rule sim5)
    qed
    moreover have "Q \<leadsto>\<^sup>^<weakBisim> P"
    proof -
      from PeqQ have "\<tau>.(Q) \<leadsto><weakBisim> P" by(simp add: congruence_def)
      thus ?thesis by(rule sim4)
    qed
    ultimately show ?thesis by(blast intro: Weak_Late_Bisim.unfoldI)
  qed
qed

lemma hennessy:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  shows "P \<approx> Q = (\<tau>.(P) \<simeq> Q \<or> P \<simeq> Q \<or> P \<simeq> \<tau>.(Q))"
proof(rule iffI)
  assume "P \<approx> Q"
  then show "\<tau>.(P) \<simeq> Q \<or> P \<simeq> Q \<or> P \<simeq> \<tau>.(Q)" by(rule hennessyLeft)
next
  assume "\<tau>.(P) \<simeq> Q \<or> P \<simeq> Q \<or> P \<simeq> \<tau>.(Q)"
  then show "P \<approx> Q" by(rule hennessyRight)
qed

end
