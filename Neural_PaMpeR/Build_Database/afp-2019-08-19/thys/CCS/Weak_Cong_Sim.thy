(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Sim
  imports Weak_Cong_Semantics Weak_Sim Strong_Sim
begin

definition weakCongSimulation :: "ccs \<Rightarrow> (ccs \<times> ccs) set \<Rightarrow> ccs \<Rightarrow> bool"   ("_ \<leadsto><_> _" [80, 80, 80] 80)
where
  "P \<leadsto><Rel> Q \<equiv> \<forall>a Q'. Q \<longmapsto>a \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>a \<prec> P' \<and> (P', Q') \<in> Rel)"

lemma weakSimI[case_names Sim]:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "\<And>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto><Rel> Q"
using assms
by(auto simp add: weakCongSimulation_def)

lemma weakSimE:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   \<alpha>   :: act
  and   Q'  :: ccs

  assumes "P \<leadsto><Rel> Q"
  and     "Q \<longmapsto>\<alpha> \<prec> Q'"

  obtains P' where "P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
using assms
by(auto simp add: weakCongSimulation_def)

lemma simWeakSim:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "P \<leadsto>[Rel] Q"
  
  shows "P \<leadsto><Rel> Q"
using assms
by(rule_tac weakSimI, auto)
  (blast dest: simE transitionWeakCongTransition)

lemma weakCongSimWeakSim:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "P \<leadsto><Rel> Q"
  
  shows "P \<leadsto>\<^sup>^<Rel> Q"
using assms
by(rule_tac Weak_Sim.weakSimI, auto)
  (blast dest: weakSimE weakCongTransitionWeakTransition)

lemma test:
  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "P = P' \<or> (\<exists>P''. P \<longmapsto>\<tau> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P')"
using assms
by(induct rule: tauChainInduct) auto

lemma tauChainCasesSym[consumes 1, case_names cTauNil cTauStep]:
  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "Prop P"
  and     "\<And>P''. \<lbrakk>P \<longmapsto>\<tau> \<prec> P''; P'' \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> Prop P'"

  shows "Prop P'"
using assms
by(blast dest: test)

lemma simE2:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   \<alpha>   :: act
  and   Q'  :: ccs

  assumes "P \<leadsto><Rel> Q"
  and     "Q \<Longrightarrow>\<alpha> \<prec> Q'"
  and     Sim: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S"
  
  obtains P' where "P \<Longrightarrow>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
proof -
  assume Goal: "\<And>P'. \<lbrakk>P \<Longrightarrow>\<alpha> \<prec> P'; (P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  from \<open>Q \<Longrightarrow>\<alpha> \<prec> Q'\<close> obtain Q''' Q''
    where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''" and Q'''Trans: "Q''' \<longmapsto>\<alpha> \<prec> Q''" and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(rule weakCongTransE)
  from QChain Q'''Trans show ?thesis
  proof(induct rule: tauChainCasesSym)
    case cTauNil
    from \<open>P \<leadsto><Rel> Q\<close> \<open>Q \<longmapsto>\<alpha> \<prec> Q''\<close> obtain P''' where PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'''" and "(P''', Q'') \<in> Rel"
      by(blast dest: weakSimE)
    moreover from Q''Chain \<open>(P''', Q'') \<in> Rel\<close> Sim obtain P' where P''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'" and "(P', Q') \<in> Rel"
      by(rule simTauChain)
    with PTrans P''Chain show ?thesis
      by(force intro: Goal simp add: weakCongTrans_def weakTrans_def)
  next
    case(cTauStep Q'''')
    from \<open>P \<leadsto><Rel> Q\<close> \<open>Q \<longmapsto>\<tau> \<prec> Q''''\<close> obtain P'''' where  PChain: "P \<Longrightarrow>\<tau> \<prec> P''''" and "(P'''', Q'''') \<in> Rel"
      by(drule_tac weakSimE) auto
    from \<open>Q'''' \<Longrightarrow>\<^sub>\<tau> Q'''\<close> \<open>(P'''', Q'''') \<in> Rel\<close> Sim obtain P''' where P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P'''" and "(P''', Q''') \<in> Rel"
      by(rule simTauChain)
    from \<open>(P''', Q''') \<in> Rel\<close> have "P''' \<leadsto>\<^sup>^<Rel> Q'''" by(rule Sim)
    then obtain P'' where P'''Trans: "P''' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P''" and "(P'', Q'') \<in> Rel" using Q'''Trans by(rule Weak_Sim.weakSimE)
    from Q''Chain \<open>(P'', Q'') \<in> Rel\<close> Sim obtain P' where P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'" and "(P', Q') \<in> Rel"
      by(rule simTauChain)
    from PChain P''''Chain P'''Trans P''Chain
    have "P \<Longrightarrow>\<alpha> \<prec> P'"
      apply(auto simp add: weakCongTrans_def weakTrans_def)
      apply(rule_tac x=P''aa in exI)
      apply auto
      defer
      apply blast
      by(auto simp add: tauChain_def)

    with \<open>(P', Q') \<in> Rel\<close> show ?thesis
      by(force intro: Goal simp add: weakCongTrans_def weakTrans_def)
  qed
qed

lemma reflexive:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto><Rel> P"
using assms
by(auto simp add: weakCongSimulation_def intro: transitionWeakCongTransition)
  
lemma transitive:
  fixes P     :: ccs
  and   Rel   :: "(ccs \<times> ccs) set"
  and   Q     :: ccs
  and   Rel'  :: "(ccs \<times> ccs) set"
  and   R     :: ccs
  and   Rel'' :: "(ccs \<times> ccs) set"
  
  assumes "P \<leadsto><Rel> Q"
  and     "Q \<leadsto><Rel'> R"
  and     "Rel O Rel' \<subseteq> Rel''"
  and     "\<And>S T. (S, T) \<in> Rel \<Longrightarrow> S \<leadsto>\<^sup>^<Rel> T"
  
  shows "P \<leadsto><Rel''> R"
proof(induct rule: weakSimI)
  case(Sim \<alpha> R')
  thus ?case using assms
    apply(drule_tac Q=R in weakSimE, auto)
    by(drule_tac Q=Q in simE2) auto
qed

lemma weakMonotonic:
  fixes P :: ccs
  and   A :: "(ccs \<times> ccs) set"
  and   Q :: ccs
  and   B :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto><A> Q"
  and     "A \<subseteq> B"

  shows "P \<leadsto><B> Q"
using assms
by(fastforce simp add: weakCongSimulation_def)

end
