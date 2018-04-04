(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Sim
  imports Weak_Semantics Strong_Sim
begin

definition weakSimulation :: "ccs \<Rightarrow> (ccs \<times> ccs) set \<Rightarrow> ccs \<Rightarrow> bool"   ("_ \<leadsto>\<^sup>^<_> _" [80, 80, 80] 80)
where
  "P \<leadsto>\<^sup>^<Rel> Q \<equiv> \<forall>a Q'. Q \<longmapsto>a \<prec> Q' \<longrightarrow> (\<exists>P'. P \<Longrightarrow>\<^sup>^a \<prec> P' \<and> (P', Q') \<in> Rel)"

lemma weakSimI[case_names Sim]:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "\<And>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>\<^sup>^<Rel> Q"
using assms
by(auto simp add: weakSimulation_def)

lemma weakSimE:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   \<alpha>   :: act
  and   Q'  :: ccs

  assumes "P \<leadsto>\<^sup>^<Rel> Q"
  and     "Q \<longmapsto>\<alpha> \<prec> Q'"

  obtains P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
using assms
by(auto simp add: weakSimulation_def)

lemma simTauChain:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   Q'  :: ccs

  assumes "Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "(P, Q) \<in> Rel"
  and     Sim: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S"

  obtains P' where "P \<Longrightarrow>\<^sub>\<tau> P'" and "(P', Q') \<in> Rel"
using `Q \<Longrightarrow>\<^sub>\<tau> Q'` `(P, Q) \<in> Rel`
proof(induct arbitrary: thesis rule: tauChainInduct)
  case Base
  from `(P, Q) \<in> Rel` show ?case
    by(force intro: Base)
next
  case(Step Q'' Q')
  from `(P, Q) \<in> Rel` obtain P'' where "P \<Longrightarrow>\<^sub>\<tau> P''" and "(P'', Q'') \<in> Rel"
    by(blast intro: Step)
  from `(P'', Q'') \<in> Rel` have "P'' \<leadsto>\<^sup>^<Rel> Q''" by(rule Sim)
  then obtain P' where "P'' \<Longrightarrow>\<^sup>^\<tau> \<prec> P'" and "(P', Q') \<in> Rel" using `Q'' \<longmapsto>\<tau> \<prec> Q'` by(rule weakSimE)
  with `P \<Longrightarrow>\<^sub>\<tau> P''` show thesis
    by(force simp add: weakTrans_def weakCongTrans_def intro: Step)
qed

lemma simE2:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   \<alpha>   :: act
  and   Q'  :: ccs

  assumes "(P, Q) \<in> Rel"
  and     "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"
  and     Sim: "\<And>R S. (R, S) \<in> Rel \<Longrightarrow> R \<leadsto>\<^sup>^<Rel> S"
  
  obtains P' where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
proof -
  assume Goal: "\<And>P'. \<lbrakk>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'; (P', Q') \<in> Rel\<rbrakk> \<Longrightarrow> thesis"
  moreover from `Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'` have "\<exists>P'. P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
  proof(induct rule: weakTransCases)
    case Base
    from `(P, Q) \<in> Rel` show ?case by force
  next
    case Step
    from `Q \<Longrightarrow>\<alpha> \<prec> Q'` obtain Q''' Q''
    where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''" and Q'''Trans: "Q''' \<longmapsto>\<alpha> \<prec> Q''" and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
      by(rule weakCongTransE)
    from QChain `(P, Q) \<in> Rel` Sim obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''" and "(P''', Q''') \<in> Rel"
      by(rule simTauChain)
    from `(P''', Q''') \<in> Rel` have "P''' \<leadsto>\<^sup>^<Rel> Q'''" by(rule Sim)
    then obtain P'' where P'''Trans: "P''' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P''" and "(P'', Q'') \<in> Rel" using Q'''Trans by(rule weakSimE)
    from Q''Chain `(P'', Q'') \<in> Rel` Sim obtain P' where P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'" and "(P', Q') \<in> Rel"
      by(rule simTauChain)
    from P'''Trans P''Chain Step show ?thesis
    proof(induct rule: weakTransCases)
      case Base
      from PChain `P''' \<Longrightarrow>\<^sub>\<tau> P'` have "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P'"
      proof(induct rule: tauChainInduct)
        case Base
        from `P \<Longrightarrow>\<^sub>\<tau> P'` show ?case
        proof(induct rule: tauChainInduct)
          case Base
          show ?case by simp
        next
          case(Step P' P'')
          thus ?case by(fastforce simp add: weakTrans_def weakCongTrans_def)
        qed
      next
        case(Step P''' P'')
        thus ?case by(fastforce simp add: weakTrans_def weakCongTrans_def)
      qed
      with `(P', Q') \<in> Rel` show ?case by blast
    next
      case Step
      thus ?case using `(P', Q') \<in> Rel` PChain
        by(rule_tac x=P' in exI) (force simp add: weakTrans_def weakCongTrans_def)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma reflexive:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>\<^sup>^<Rel> P"
using assms
by(auto simp add: weakSimulation_def intro: transitionWeakCongTransition weakCongTransitionWeakTransition)
  
lemma transitive:
  fixes P     :: ccs
  and   Rel   :: "(ccs \<times> ccs) set"
  and   Q     :: ccs
  and   Rel'  :: "(ccs \<times> ccs) set"
  and   R     :: ccs
  and   Rel'' :: "(ccs \<times> ccs) set"
  
  assumes "(P, Q) \<in> Rel"
  and     "Q \<leadsto>\<^sup>^<Rel'> R"
  and     "Rel O Rel' \<subseteq> Rel''"
  and     "\<And>S T. (S, T) \<in> Rel \<Longrightarrow> S \<leadsto>\<^sup>^<Rel> T"
  
  shows "P \<leadsto>\<^sup>^<Rel''> R"
proof(induct rule: weakSimI)
  case(Sim \<alpha> R')
  thus ?case using assms
    apply(drule_tac Q=R in weakSimE, auto)
    by(drule_tac Q=Q in simE2, auto)
qed

lemma weakMonotonic:
  fixes P :: ccs
  and   A :: "(ccs \<times> ccs) set"
  and   Q :: ccs
  and   B :: "(ccs \<times> ccs) set"

  assumes "P \<leadsto>\<^sup>^<A> Q"
  and     "A \<subseteq> B"

  shows "P \<leadsto>\<^sup>^<B> Q"
using assms
by(fastforce simp add: weakSimulation_def)

lemma simWeakSim:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "P \<leadsto>[Rel] Q"
  
  shows "P \<leadsto>\<^sup>^<Rel> Q"
using assms
by(rule_tac weakSimI, auto)
  (blast dest: simE transitionWeakTransition)

end
