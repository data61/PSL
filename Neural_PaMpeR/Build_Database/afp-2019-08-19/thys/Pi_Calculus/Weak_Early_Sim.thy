(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Sim
  imports Weak_Early_Semantics Strong_Early_Sim_Pres
begin

definition weakSimulation :: "pi \<Rightarrow> (pi \<times> pi) set \<Rightarrow> pi \<Rightarrow> bool" ("_ \<leadsto><_> _" [80, 80, 80] 80)
  where "P \<leadsto><Rel> Q \<equiv> (\<forall>a x Q'. Q \<longmapsto>a<\<nu>x> \<prec> Q' \<and> x \<sharp> P \<longrightarrow> (\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel)) \<and>
                       (\<forall>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel))"

lemma monotonic: 
  fixes A  :: "(pi \<times> pi) set"
  and   B  :: "(pi \<times> pi) set"
  and   P  :: pi
  and   P' :: pi

  assumes "P \<leadsto><A> P'"
  and     "A \<subseteq> B"

  shows "P \<leadsto><B> P'"
using assms
by(simp add: weakSimulation_def) blast

lemma simCasesCont[consumes 1, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes Eqvt:  "eqvt Rel"
  and     Bound: "\<And>a x Q'. \<lbrakk>Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<sharp> C\<rbrakk> \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto><Rel> Q"
proof(auto simp add: weakSimulation_def)
  fix a x Q'
  assume QTrans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'" and "x \<sharp> P"
  obtain c::name where "c \<sharp> P" and "c \<sharp> Q" and "c \<noteq> a" and "c \<sharp> Q'" and "c \<sharp> C" and "c \<noteq> x"
    by(generate_fresh "name") auto

  from QTrans \<open>c \<sharp> Q'\<close> have "Q \<longmapsto> a<\<nu>c> \<prec> ([(x, c)] \<bullet> Q')" by(simp add: alphaBoundOutput)
  then obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>c> \<prec> P'" and P'RelQ': "(P', [(x, c)] \<bullet> Q') \<in> Rel"
    using \<open>c \<sharp> P\<close> \<open>c \<sharp> Q\<close> \<open>c \<noteq> a\<close> \<open>c \<sharp> C\<close>
    by(drule_tac Bound) auto

  from PTrans \<open>x \<sharp> P\<close> \<open>c \<noteq> x\<close> have "P \<Longrightarrow>a<\<nu>x> \<prec> ([(x, c)] \<bullet> P')"
    by(force intro: weakTransitionAlpha simp add: name_swap)
  moreover from Eqvt P'RelQ' have "([(x, c)] \<bullet> P', [(x, c)] \<bullet> [(x, c)] \<bullet> Q') \<in> Rel"
    by(rule eqvtRelI)
  hence "([(x, c)] \<bullet> P', Q') \<in> Rel" by simp
  ultimately show "\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
    by blast
next
  fix \<alpha> Q'
  assume "Q \<longmapsto>\<alpha> \<prec> Q'"
  thus "\<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
    by(rule Free)
qed

lemma simCases[case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes "\<And>Q' a x. \<lbrakk>Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P\<rbrakk> \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     "\<And>Q' \<alpha>. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto><Rel> Q"
using assms
by(auto simp add: weakSimulation_def)

lemma simE:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   Q'  :: pi

  assumes "P \<leadsto><Rel> Q"

  shows "Q \<longmapsto>a<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and   "Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
using assms by(simp add: weakSimulation_def)+

lemma weakSimTauChain:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Rel' :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   Q'  :: pi

  assumes QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     PRelQ: "(P, Q) \<in> Rel"
  and     PSimQ: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel> S"

  shows "\<exists>P'. P \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel"
proof -
  from QChain show ?thesis
  proof(induct rule: tauChainInduct)
    case id
    moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
    ultimately show ?case using PSimQ PRelQ by blast
  next
    case(ih Q' Q'')
    have "\<exists>P'. P \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel" by fact
    then obtain P' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'" and P'Rel'Q': "(P', Q') \<in> Rel" by blast
    from P'Rel'Q' have "P' \<leadsto><Rel> Q'" by(rule PSimQ)
    moreover have Q'Trans: "Q' \<longmapsto>\<tau> \<prec> Q''" by fact
    ultimately obtain P'' where P'Trans: "P' \<Longrightarrow>\<^sup>^\<tau> \<prec> P''" and P''RelQ'': "(P'', Q'') \<in> Rel"
      by(blast dest: simE)
    from P'Trans have "P' \<Longrightarrow>\<^sub>\<tau> P''" by simp
    with PChain have "P \<Longrightarrow>\<^sub>\<tau> P''" by auto
    with P''RelQ'' show ?case by blast
  qed
qed

lemma simE2:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   Q'  :: pi

  assumes Sim: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel> S"
  and     Eqvt: "eqvt Rel"
  and     PRelQ: "(P, Q) \<in> Rel"

  shows "Q \<Longrightarrow>a<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and   "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
proof -
  assume QTrans: "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'" and "x \<sharp> P"
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a<\<nu>x> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from QChain PRelQ Sim obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''" and P'''RelQ''': "(P''', Q''') \<in> Rel" 
    by(blast dest: weakSimTauChain)

  from PChain \<open>x \<sharp> P\<close> have "x \<sharp> P'''" by(rule freshChain)
      
  from P'''RelQ''' have "P''' \<leadsto><Rel> Q'''" by(rule Sim)
  with Q'''Trans \<open>x \<sharp> P'''\<close> obtain P'' where P'''Trans: "P''' \<Longrightarrow>a<\<nu>x> \<prec> P''"
                                         and P''RelQ'': "(P'', Q'') \<in> Rel"
    by(blast dest: simE)

  from Q''Chain P''RelQ'' Sim obtain P' where P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: weakSimTauChain)
  from PChain P'''Trans P''Chain  have "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
    by(blast dest: Weak_Early_Step_Semantics.chainTransitionAppend)
  with P'RelQ' show "\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel" by blast
next
  assume "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"
  thus "\<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: transitionCases)
    case Step
    have "Q \<Longrightarrow>\<alpha> \<prec> Q'" by fact
    then obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q''" 
                           and Q''Trans: "Q'' \<longmapsto>\<alpha> \<prec> Q'''"
                           and Q'''Chain: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
      by(blast dest: transitionE)

    from QChain PRelQ Sim have "\<exists>P''. P \<Longrightarrow>\<^sub>\<tau> P'' \<and> (P'', Q'') \<in> Rel"
      by(rule weakSimTauChain)
    then obtain P'' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''" and P''RelQ'': "(P'', Q'') \<in> Rel" by blast
    from P''RelQ'' have "P'' \<leadsto><Rel> Q''" by(rule Sim)
    with Q''Trans obtain P''' where P''Trans: "P'' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'''"
                                and P'''RelQ''': "(P''', Q''') \<in> Rel"
      by(blast dest: simE)
    
    have "\<exists>P'. P''' \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel" using Q'''Chain P'''RelQ''' Sim
      by(rule weakSimTauChain)
    then obtain P' where P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    
    from PChain P''Trans P'''Chain have "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
      by(blast dest: chainTransitionAppend)
    with P'RelQ' show ?case by blast
  next
    case Stay
    have "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P" by simp
    thus ?case using PRelQ by blast
  qed
qed

lemma eqvtI:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes PSimQ: "P \<leadsto><Rel> Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel': "eqvt Rel'"

  shows "(perm \<bullet> P) \<leadsto><Rel'> (perm \<bullet> Q)"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have xFreshP: "x \<sharp> perm \<bullet> P" by fact
  have QTrans: "(perm \<bullet> Q) \<longmapsto> a<\<nu>x> \<prec> Q'" by fact

  hence "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (a<\<nu>x> \<prec> Q')" by(rule eqvts)
  hence "Q \<longmapsto> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> x)> \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  moreover from xFreshP have "(rev perm \<bullet> x) \<sharp> P" by(simp add: name_fresh_left)
  ultimately obtain P' where PTrans: "P \<Longrightarrow>(rev perm \<bullet> a)<\<nu>(rev perm \<bullet> x)> \<prec> P'"
                         and P'RelQ': "(P', rev perm \<bullet> Q') \<in> Rel" using PSimQ
    by(blast dest: simE)
  
  from PTrans have "(perm \<bullet> P) \<Longrightarrow>(perm \<bullet> rev perm \<bullet> a)<\<nu>(perm \<bullet> rev perm \<bullet> x)> \<prec> perm \<bullet> P'" 
    by(rule eqvts)
  hence "(perm \<bullet> P) \<Longrightarrow>a<\<nu>x> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  moreover from P'RelQ' RelRel' have "(P', rev perm \<bullet> Q') \<in> Rel'" by blast
  with EqvtRel' have "(perm \<bullet> P', perm \<bullet> (rev perm \<bullet> Q')) \<in> Rel'"
    by(rule eqvtRelI)
  hence "(perm \<bullet> P', Q') \<in> Rel'" by(simp add: name_per_rev)
  ultimately show ?case by blast
next
  case(Free Q' \<alpha>)
  have QTrans: "(perm \<bullet> Q) \<longmapsto> \<alpha> \<prec> Q'" by fact

  hence "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (\<alpha> \<prec> Q')" by(rule eqvts)
  hence "Q \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> (rev perm \<bullet> Q')"  by(simp add: name_rev_per)
  with PSimQ obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^ (rev perm \<bullet> \<alpha>) \<prec> P'"
                         and PRel: "(P', (rev perm \<bullet> Q')) \<in> Rel"
    by(blast dest: simE)

  from PTrans have "(perm \<bullet> P) \<Longrightarrow>\<^sup>^ (perm \<bullet> rev perm \<bullet> \<alpha>) \<prec> perm \<bullet> P'"
    by(rule Weak_Early_Semantics.eqvtI)
  hence L1: "(perm \<bullet> P) \<Longrightarrow>\<^sup>^ \<alpha> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from PRel EqvtRel' RelRel'  have "((perm \<bullet> P'), (perm \<bullet> (rev perm \<bullet> Q'))) \<in> Rel'"
    by(force intro: eqvtRelI)
  hence "((perm \<bullet> P'), Q') \<in> Rel'" by(simp add: name_per_rev)
  with L1 show ?case by blast
qed

(*****************Reflexivity and transitivity*********************)

lemma reflexive:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto><Rel> P"
using assms
by(auto intro: Weak_Early_Step_Semantics.singleActionChain
   simp add: weakSimulation_def weakFreeTransition_def)

lemma transitive:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"

  assumes QSimR: "Q \<leadsto><Rel'> R"
  and     Eqvt: "eqvt Rel"
  and     Eqvt'': "eqvt Rel''"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"
  and     Sim: "\<And>S T. (S, T) \<in> Rel \<Longrightarrow> S \<leadsto><Rel> T"
  and     PRelQ: "(P, Q) \<in> Rel"

  shows "P \<leadsto><Rel''> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: simCasesCont[where C=Q])
    case(Bound a x R')
    have RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" by fact
    from \<open>x \<sharp> Q\<close> QSimR RTrans obtain Q' where QTrans: "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
                                          and Q'Rel'R': "(Q', R') \<in> Rel'"
      by(blast dest: simE)

    from Sim Eqvt PRelQ QTrans \<open>x \<sharp> P\<close> 
    obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(drule_tac simE2) auto
(*      by(blast dest: simE2)*)
    moreover from P'RelQ' Q'Rel'R' Trans have "(P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(Free \<alpha> R')
    have RTrans: "R \<longmapsto> \<alpha> \<prec> R'" by fact
    with QSimR obtain Q' where QTrans: "Q \<Longrightarrow>\<^sup>^ \<alpha> \<prec> Q'" and Q'RelR': "(Q', R') \<in> Rel'"
      by(blast dest: simE)
    from Sim Eqvt PRelQ QTrans have "\<exists>P'. P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
      by(blast intro: simE2)
    then obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    from P'RelQ' Q'RelR' Trans have "(P', R') \<in> Rel''" by blast
    with PTrans show ?case by blast
  qed
qed

lemma strongAppend:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto><Rel> Q"
  and     QSimR: "Q \<leadsto>[Rel'] R"
  and     Eqvt'': "eqvt Rel''"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"

  shows "P \<leadsto><Rel''> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: simCasesCont[where C=Q])
    case(Bound a x R')
    have RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" by fact
    from QSimR RTrans \<open>x \<sharp> Q\<close> obtain Q' where QTrans: "Q \<longmapsto>a<\<nu>x> \<prec> Q'"
                                          and Q'Rel'R': "(Q', R') \<in> Rel'"
      by(blast dest: Strong_Early_Sim.elim)

    with PSimQ QTrans \<open>x \<sharp> P\<close> obtain P' where PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" 
      by(blast dest: simE)
    moreover from P'RelQ' Q'Rel'R' Trans have "(P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(Free \<alpha> R')
    have RTrans: "R \<longmapsto> \<alpha> \<prec> R'" by fact
    with QSimR obtain Q' where QTrans: "Q \<longmapsto>\<alpha> \<prec> Q'" and Q'RelR': "(Q', R') \<in> Rel'"
      by(blast dest: Strong_Early_Sim.elim)
    from PSimQ QTrans obtain P' where PTrans: "P \<Longrightarrow>\<^sup>^ \<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
      by(blast dest: simE)
    from P'RelQ' Q'RelR' Trans have "(P', R') \<in> Rel''" by blast
    with PTrans show ?case by blast
  qed
qed

lemma strongSimWeakSim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"

  shows "P \<leadsto><Rel> Q"
proof(induct rule: simCases)
  case(Bound Q' a x)
  have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
  with PSimQ \<open>x \<sharp> P\<close> obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: Strong_Early_Sim.elim)
  from PTrans have "P \<Longrightarrow>a<\<nu>x> \<prec>  P'"
    by(force intro: Weak_Early_Step_Semantics.singleActionChain simp add: weakFreeTransition_def)
  with P'RelQ' show ?case by blast
next
  case(Free Q' \<alpha>)
  have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  with PSimQ obtain P' where PTrans: "P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: Strong_Early_Sim.elim)
  from PTrans have "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" by(rule Weak_Early_Semantics.singleActionChain)
  with P'RelQ' show ?case by blast
qed

end
