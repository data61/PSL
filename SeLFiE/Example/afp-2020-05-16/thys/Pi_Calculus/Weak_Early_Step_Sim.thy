(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Step_Sim
  imports Weak_Early_Sim Strong_Early_Sim
begin

definition weakStepSimulation :: "pi \<Rightarrow> (pi \<times> pi) set \<Rightarrow> pi \<Rightarrow> bool" ("_ \<leadsto>\<guillemotleft>_\<guillemotright> _" [80, 80, 80] 80) where
  "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q \<equiv> (\<forall>Q' a x. Q \<longmapsto>a<\<nu>x> \<prec> Q' \<longrightarrow> x \<sharp> P \<longrightarrow> (\<exists>P' . P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel)) \<and>
                         (\<forall>Q' \<alpha>. Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel))"

lemma monotonic: 
  fixes A  :: "(pi \<times> pi) set"
  and   B  :: "(pi \<times> pi) set"
  and   P  :: pi
  and   P' :: pi

  assumes "P \<leadsto>\<guillemotleft>A\<guillemotright> P'"
  and     "A \<subseteq> B"

  shows "P \<leadsto>\<guillemotleft>B\<guillemotright> P'"
using assms
by(simp add: weakStepSimulation_def) blast

lemma simCasesCont[consumes 1, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes Eqvt:  "eqvt Rel"
  and     Bound: "\<And>a x Q'. \<lbrakk>x \<sharp> C; Q \<longmapsto> a<\<nu>x> \<prec> Q'\<rbrakk> \<Longrightarrow> \<exists>P'. P \<Longrightarrow> a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
proof -
  from Free show ?thesis
  proof(auto simp add: weakStepSimulation_def)
    fix Q' a x
    assume xFreshP: "(x::name) \<sharp> P"
    assume Trans: "Q \<longmapsto> a<\<nu>x> \<prec> Q'"
    have "\<exists>c::name. c \<sharp> (P, Q', x, C)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ': "c \<sharp> Q'" and cFreshC: "c \<sharp> C"
                          and cineqx: "c \<noteq> x"
      by(force simp add: fresh_prod)

    from Trans cFreshQ' have "Q \<longmapsto> a<\<nu>c> \<prec> ([(x, c)] \<bullet> Q')" by(simp add: alphaBoundOutput)
    with cFreshC have "\<exists>P'. P \<Longrightarrow> a<\<nu>c> \<prec> P' \<and> (P', [(x, c)] \<bullet> Q') \<in> Rel"
      by(rule Bound)
    then obtain P' where PTrans: "P \<Longrightarrow> a<\<nu>c> \<prec> P'" and P'RelQ': "(P', [(x, c)] \<bullet> Q') \<in> Rel"
      by blast

    from PTrans \<open>x \<sharp> P\<close> \<open>c \<noteq> x\<close> have "P \<Longrightarrow>a<\<nu>x> \<prec> ([(x, c)] \<bullet> P')" 
      by(simp add: weakTransitionAlpha name_swap)
    moreover from Eqvt P'RelQ' have "([(x, c)] \<bullet> P', [(x, c)] \<bullet> [(x, c)] \<bullet> Q') \<in> Rel"
      by(rule eqvtRelI)
    with \<open>c \<noteq> x\<close> have "([(x, c)] \<bullet> P', Q') \<in> Rel"
      by simp
    ultimately show "\<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel" by blast
  qed
qed

lemma simCases[consumes 0, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes "\<And>a x Q'. \<lbrakk>Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P\<rbrakk> \<Longrightarrow> \<exists>P'. P \<Longrightarrow> a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
using assms
by(auto simp add: weakStepSimulation_def)

lemma simE:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   Q'  :: pi

  assumes "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "Q \<longmapsto>a<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and   "Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
using assms by(simp add: weakStepSimulation_def)+

lemma simE2:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   Q'  :: pi

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     Sim: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto><Rel> S"
  and     Eqvt: "eqvt Rel"
  and     PRelQ: "(P, Q) \<in> Rel"

  shows "Q \<Longrightarrow>a<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<Longrightarrow>a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and   "Q \<Longrightarrow>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
proof -
  assume QTrans: "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  assume "x \<sharp> P"
    
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q''"
                                        and Q''Trans: "Q'' \<longmapsto>a<\<nu>x> \<prec> Q'''"
                                        and Q'''Chain: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from QChain PRelQ Sim have "\<exists>P''. P \<Longrightarrow>\<^sub>\<tau> P'' \<and> (P'', Q'') \<in> Rel"
    by(rule weakSimTauChain)
  then obtain P'' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''" and P''RelQ'': "(P'', Q'') \<in> Rel" by blast
  from PChain \<open>x \<sharp> P\<close> have xFreshP'': "x \<sharp> P''" by(rule freshChain)
  
  from P''RelQ'' have "P'' \<leadsto><Rel> Q''" by(rule Sim)
  with Q''Trans xFreshP'' obtain P''' where P''Trans: "P'' \<Longrightarrow>a<\<nu>x> \<prec> P'''"
                                        and P'''RelQ''': "(P''', Q''') \<in> Rel"
    by(blast dest: Weak_Early_Sim.simE)

  have "\<exists>P'. P''' \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel" using Q'''Chain P'''RelQ''' Sim
    by(rule weakSimTauChain)
  then obtain P' where P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    
  from PChain P''Trans P'''Chain have "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
    by(blast dest: Weak_Early_Step_Semantics.chainTransitionAppend)
  with P'RelQ' show "\<exists>P'. P \<Longrightarrow> a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
    by blast
next
  assume "Q \<Longrightarrow>\<alpha> \<prec> Q'"

  then obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q''" 
                         and Q''Trans: "Q'' \<longmapsto>\<alpha> \<prec> Q'''"
                         and Q'''Chain: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  from QChain Q''Trans Q'''Chain show "\<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct arbitrary: \<alpha> Q''' Q' rule: tauChainInduct)
    case id
    from PSimQ \<open>Q \<longmapsto>\<alpha> \<prec> Q'''\<close> have "\<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q''') \<in> Rel"
      by(blast dest: simE)
    then obtain P''' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'''" and P'RelQ''': "(P''', Q''') \<in> Rel"
      by blast
    
    have "\<exists>P'. P''' \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel" using \<open>Q''' \<Longrightarrow>\<^sub>\<tau> Q'\<close> P'RelQ''' Sim
      by(rule Weak_Early_Sim.weakSimTauChain)
    then obtain P' where P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    
    from P'''Chain PTrans have "P \<Longrightarrow>\<alpha> \<prec> P'"
      by(blast dest: Weak_Early_Step_Semantics.chainTransitionAppend)
    
    with P'RelQ' show ?case by blast
  next
    case(ih Q'''' Q'' \<alpha> Q''' Q')
    have "Q'' \<Longrightarrow>\<^sub>\<tau> Q''" by simp
    with \<open>Q'''' \<longmapsto>\<tau> \<prec> Q''\<close> obtain P'' where PChain: "P \<Longrightarrow>\<tau> \<prec>  P''" and P''RelQ'': "(P'', Q'') \<in> Rel"
      by(drule_tac ih) auto

    from P''RelQ'' have "P'' \<leadsto><Rel> Q''" by(rule Sim)
    hence "\<exists>P'''. P'' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P''' \<and> (P''', Q''') \<in> Rel" using \<open>Q'' \<longmapsto>\<alpha> \<prec> Q'''\<close>
      by(rule Weak_Early_Sim.simE)
    then obtain P''' where P''Trans: "P'' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'''"
                       and P'''RelQ''': "(P''', Q''') \<in> Rel"
      by blast
    from \<open>Q''' \<Longrightarrow>\<^sub>\<tau> Q'\<close> P'''RelQ''' Sim have "\<exists>P'. P''' \<Longrightarrow>\<^sub>\<tau> P' \<and> (P', Q') \<in> Rel"
      by(rule Weak_Early_Sim.weakSimTauChain)
    then obtain P' where P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
                     and P'RelQ': "(P', Q') \<in> Rel"
      by blast
    from PChain P''Trans have "P \<Longrightarrow>\<alpha> \<prec> P'''"
      apply(auto simp add: freeTransition_def weakFreeTransition_def)
      apply(drule tauActTauChain, auto)
      by(rule_tac x=P'''aa in exI) auto
    hence "P \<Longrightarrow>\<alpha> \<prec> P'" using P'''Chain
      by(rule Weak_Early_Step_Semantics.chainTransitionAppend)
    with P'RelQ' show ?case by blast
  qed
qed

lemma eqvtI:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel': "eqvt Rel'"

  shows "(perm \<bullet> P) \<leadsto>\<guillemotleft>Rel'\<guillemotright> (perm \<bullet> Q)"
proof(induct rule: simCases)
  case(Bound a x Q')
  have xFreshP: "x \<sharp> perm \<bullet> P" by fact
  have QTrans: "(perm \<bullet> Q) \<longmapsto> a<\<nu>x> \<prec> Q'" by fact

  hence "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (a<\<nu>x> \<prec> Q')" by(rule eqvt)
  hence "Q \<longmapsto> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> x)> \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  moreover from xFreshP have "(rev perm \<bullet> x) \<sharp> P" by(simp add: name_fresh_left)
  ultimately obtain P' where PTrans: "P \<Longrightarrow> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> x)> \<prec> P'"
                         and P'RelQ': "(P', rev perm \<bullet> Q') \<in> Rel" using PSimQ
    by(blast dest: simE)
  
  from PTrans have "(perm \<bullet> P) \<Longrightarrow>(perm \<bullet> rev perm \<bullet> a)<\<nu>(perm \<bullet> rev perm \<bullet> x)> \<prec> perm \<bullet> P'" 
    by(rule Weak_Early_Step_Semantics.eqvtI)
  hence L1: "(perm \<bullet> P) \<Longrightarrow> a<\<nu>x> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from P'RelQ' RelRel' have "(P', rev perm \<bullet> Q') \<in> Rel'" by blast
  with EqvtRel' have "(perm \<bullet> P', perm \<bullet> (rev perm \<bullet> Q')) \<in> Rel'"
    by(rule eqvtRelI)
  hence "(perm \<bullet> P', Q') \<in> Rel'" by(simp add: name_per_rev)
  with L1 show ?case by blast
next
  case(Free \<alpha> Q')
  have QTrans: "(perm \<bullet> Q) \<longmapsto> \<alpha> \<prec> Q'" by fact

  hence "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (\<alpha> \<prec> Q')" by(rule eqvts)
  hence "Q \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> (rev perm \<bullet> Q')"  by(simp add: name_rev_per)
  with PSimQ obtain P' where PTrans: "P \<Longrightarrow> (rev perm \<bullet> \<alpha>) \<prec> P'"
                         and PRel: "(P', (rev perm \<bullet> Q')) \<in> Rel"
    by(blast dest: simE)

  from PTrans have "(perm \<bullet> P) \<Longrightarrow>(perm \<bullet> rev perm \<bullet> \<alpha>) \<prec> perm \<bullet> P'"
    by(rule Weak_Early_Step_Semantics.eqvtI)
  hence L1: "(perm \<bullet> P) \<Longrightarrow> \<alpha> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
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

  shows "P \<leadsto>\<guillemotleft>Rel\<guillemotright> P"
using assms
by(auto intro: Weak_Early_Step_Semantics.singleActionChain
   simp add: weakStepSimulation_def weakFreeTransition_def)

lemma transitive:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
  and     QSimR: "Q \<leadsto>\<guillemotleft>Rel'\<guillemotright> R"
  and     Eqvt: "eqvt Rel"
  and     Eqvt'': "eqvt Rel''"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"
  and     Sim: "\<And>S T. (S, T) \<in> Rel \<Longrightarrow> S \<leadsto><Rel> T"
  and     PRelQ: "(P, Q) \<in> Rel"

  shows "P \<leadsto>\<guillemotleft>Rel''\<guillemotright> R"
proof -
  from Eqvt'' show ?thesis
  proof(induct rule: simCasesCont[of _ "(P, Q)"])
    case(Bound a x R')
    have "x \<sharp> (P, Q)" by fact
    hence xFreshP: "x \<sharp> P" and xFreshQ: "x \<sharp> Q" by(simp add: fresh_prod)+
    have RTrans: "R \<longmapsto>a<\<nu>x> \<prec> R'" by fact
    from xFreshQ QSimR RTrans obtain Q' where QTrans: "Q \<Longrightarrow> a<\<nu>x> \<prec> Q'"
                                          and Q'Rel'R': "(Q', R') \<in> Rel'"
      by(blast dest: simE)

    with PSimQ Sim Eqvt PRelQ QTrans xFreshP have "\<exists>P'. P \<Longrightarrow> a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
      by(blast intro: simE2)
    then obtain P' where PTrans: "P \<Longrightarrow> a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    moreover from P'RelQ' Q'Rel'R' Trans have "(P', R') \<in> Rel''" by blast
    ultimately show ?case by blast
  next
    case(Free \<alpha> R')
    have RTrans: "R \<longmapsto> \<alpha> \<prec> R'" by fact
    with QSimR obtain Q' where QTrans: "Q \<Longrightarrow> \<alpha> \<prec> Q'" and Q'RelR': "(Q', R') \<in> Rel'"
      by(blast dest: simE)
    from PSimQ Sim Eqvt PRelQ QTrans have "\<exists>P'. P \<Longrightarrow> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
      by(blast intro: simE2)
    then obtain P' where PTrans: "P \<Longrightarrow> \<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    from P'RelQ' Q'RelR' Trans have "(P', R') \<in> Rel''" by blast
    with PTrans show ?case by blast
  qed
qed

lemma strongSimWeakSim:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"

  shows "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"
proof(induct rule: simCases)
  case(Bound a x Q')
  have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" and "x \<sharp> P" by fact+
  with PSimQ obtain P' where PTrans: "P \<longmapsto>a<\<nu>x> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: Strong_Early_Sim.elim)
  from PTrans have "P \<Longrightarrow>a<\<nu>x> \<prec>  P'"
    by(force intro: Weak_Early_Step_Semantics.singleActionChain simp add: weakFreeTransition_def)
  with P'RelQ' show ?case by blast
next
  case(Free \<alpha> Q')
  have "Q \<longmapsto>\<alpha> \<prec> Q'" by fact
  with PSimQ obtain P' where PTrans: "P \<longmapsto>\<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel"
    by(blast dest: Strong_Early_Sim.elim)
  from PTrans have "P \<Longrightarrow>\<alpha> \<prec> P'" by(rule Weak_Early_Step_Semantics.singleActionChain)
  with P'RelQ' show ?case by blast
qed

lemma weakSimWeakEqSim:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"

  assumes "P \<leadsto>\<guillemotleft>Rel\<guillemotright> Q"

  shows "P \<leadsto><Rel> Q"
using assms
by(force simp add: weakStepSimulation_def Weak_Early_Sim.weakSimulation_def weakFreeTransition_def)

end


