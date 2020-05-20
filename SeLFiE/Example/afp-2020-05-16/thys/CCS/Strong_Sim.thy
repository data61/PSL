(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Sim
  imports Agent
begin

definition simulation :: "ccs \<Rightarrow> (ccs \<times> ccs) set \<Rightarrow> ccs \<Rightarrow> bool"   ("_ \<leadsto>[_] _" [80, 80, 80] 80)
where
  "P \<leadsto>[Rel] Q \<equiv> \<forall>a Q'. Q \<longmapsto>a \<prec> Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>a \<prec> P' \<and> (P', Q') \<in> Rel)"

lemma simI[case_names Sim]:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs

  assumes "\<And>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>[Rel] Q"
using assms
by(auto simp add: simulation_def)

lemma simE:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  and   Q   :: ccs
  and   \<alpha>   :: act
  and   Q'  :: ccs

  assumes "P \<leadsto>[Rel] Q"
  and     "Q \<longmapsto>\<alpha> \<prec> Q'"

  obtains P' where "P \<longmapsto>\<alpha> \<prec> P'" and "(P', Q') \<in> Rel"
using assms
by(auto simp add: simulation_def)

lemma reflexive:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P"
using assms
by(auto simp add: simulation_def)
  
lemma transitive:
  fixes P     :: ccs
  and   Rel   :: "(ccs \<times> ccs) set"
  and   Q     :: ccs
  and   Rel'  :: "(ccs \<times> ccs) set"
  and   R     :: ccs
  and   Rel'' :: "(ccs \<times> ccs) set"
  
  assumes "P \<leadsto>[Rel] Q"
  and     "Q \<leadsto>[Rel'] R"
  and     "Rel O Rel' \<subseteq> Rel''"
  
  shows "P \<leadsto>[Rel''] R"
using assms
by(force simp add: simulation_def)

end


