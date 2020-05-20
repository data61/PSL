section "Bisimilarity, abstractly"

theory Bisim 
imports Interface
begin

type_synonym 'a rel = "('a * 'a) set"  
type_synonym ('cmd,'state)config = "'cmd * 'state" 

definition mono where 
"mono Retr \<equiv> 
 \<forall> theta theta'. theta \<le> theta' \<longrightarrow> Retr theta \<le> Retr theta'"

definition simul where
"simul Retr theta \<equiv> theta \<le> Retr theta"

definition bisim where 
"bisim Retr theta \<equiv> sym theta \<and> simul Retr theta"

lemma mono_Union:
assumes "mono Retr"
shows "Union (Retr ` Theta) \<le> Retr (Union Theta)"
proof-
  have "\<forall> theta' \<in> Retr ` Theta. theta' \<subseteq> Retr (Union Theta)"
  using assms unfolding mono_def by blast
  thus ?thesis by blast 
qed

lemma mono_Un:
assumes "mono Retr"
shows "Retr theta Un Retr theta' \<subseteq> Retr (theta Un theta')"
using assms unfolding mono_def
by (metis Un_least Un_upper1 Un_upper2)

lemma sym_Union:
assumes "\<And>theta. theta \<in> Theta \<Longrightarrow> sym theta"
shows "sym (Union Theta)"
using assms unfolding sym_def by blast

lemma sym_Un:
assumes "sym theta1" and "sym theta2"
shows "sym (theta1 Un theta2)"
using assms sym_Union[of "{theta1,theta2}"] by auto

lemma simul_Union:
assumes "mono Retr"
and "\<And>theta. theta \<in> Theta \<Longrightarrow> simul Retr theta"
shows "simul Retr (Union Theta)"
proof-
  have "\<forall> theta \<in> Theta. theta \<subseteq> Retr theta"
  using assms unfolding simul_def by blast
  hence "Union Theta \<subseteq> Union (Retr ` Theta)" by blast
  also have "... \<subseteq> Retr (Union Theta)" using mono_Union assms unfolding mono_def by auto
  finally have "Union Theta \<subseteq> Retr (Union Theta)" .
  thus ?thesis unfolding simul_def by simp
qed

lemma simul_Un:
assumes "mono Retr" and "simul Retr theta1" and "simul Retr theta2"
shows "simul Retr (theta1 Un theta2)"
using assms simul_Union[of Retr "{theta1,theta2}"] by auto

lemma bisim_Union:
assumes "mono Retr" and "\<And>theta. theta \<in> Theta \<Longrightarrow> bisim Retr theta"
shows "bisim Retr (Union Theta)"
using assms unfolding bisim_def
using sym_Union simul_Union by blast

lemma bisim_Un:
assumes "mono Retr" and "bisim Retr theta1" and "bisim Retr theta2"
shows "bisim Retr (theta1 Un theta2)"
using assms bisim_Union[of Retr "{theta1,theta2}"] by auto

definition bis where 
"bis Retr \<equiv> Union {theta. bisim Retr theta}"

lemma bisim_bis[simp]:
assumes "mono Retr" 
shows "bisim Retr (bis Retr)"
using assms unfolding mono_def
by (metis CollectD assms bis_def bisim_Union)

corollary sym_bis[simp]: "mono Retr \<Longrightarrow> sym (bis Retr)"
and simul_bis[simp]: "mono Retr \<Longrightarrow> simul Retr (bis Retr)"
using bisim_bis unfolding bisim_def by auto

lemma bis_raw_coind:
assumes "mono Retr" and "sym theta" and "theta \<subseteq> Retr theta"
shows "theta \<subseteq> bis Retr"
using assms unfolding mono_def bis_def bisim_def simul_def by blast

lemma bis_prefix[simp]:
assumes "mono Retr"   
shows "bis Retr \<subseteq> Retr (bis Retr)"
by (metis assms bisim_bis bisim_def simul_def)

lemma bis_coind:
assumes *: "mono Retr" and "sym theta" and **: "theta \<subseteq> Retr (theta Un (bis Retr))"
shows "theta \<subseteq> bis Retr"
proof-
  let ?theta' = "theta Un (bis Retr)"
  have "sym ?theta'" by (metis Bisim.sym_Un sym_bis assms)
  moreover have "?theta' \<subseteq> Retr ?theta'"
  by (metis assms mono_Un Un_least bis_prefix le_supI2 subset_trans)
  ultimately show ?thesis using * bis_raw_coind by blast
qed  

lemma bis_coind2:
assumes *: "mono Retr" and 
**: "theta \<subseteq> Retr (theta Un (bis Retr))" and 
***: "theta ^-1 \<subseteq> Retr ((theta ^-1) Un (bis Retr))"
shows "theta \<subseteq> bis Retr"
proof-
  let ?th = "theta Un theta ^-1"
  have "sym ?th" by (metis sym_Un_converse)
  moreover
  {have "?th \<subseteq> Retr (theta Un (bis Retr)) Un Retr (theta ^-1 Un (bis Retr))" 
   using ** *** Un_mono by blast
   also have "... \<subseteq> Retr ((theta Un (bis Retr)) Un (theta ^-1 Un (bis Retr)))" 
   using * mono_Un by blast
   also have "... = Retr (?th Un (bis Retr))" by (metis Un_assoc Un_commute Un_left_absorb)
   finally have "?th \<subseteq> Retr (?th Un (bis Retr))" .
  }
  ultimately have "?th \<subseteq> bis Retr" using assms bis_coind by blast
  thus ?thesis by blast
qed

lemma bis_raw_coind2:
assumes *: "mono Retr" and 
**: "theta \<subseteq> Retr theta" and 
***: "theta ^-1 \<subseteq> Retr (theta ^-1)"
shows "theta \<subseteq> bis Retr"
proof-
  have "theta \<subseteq> Retr (theta Un (bis Retr))" and 
  "theta ^-1 \<subseteq> Retr ((theta ^-1) Un (bis Retr))"
  using assms by(metis mono_Un le_supI1 subset_trans)+
  thus ?thesis using * bis_coind2 by blast
qed

lemma mono_bis:
assumes "mono Retr1"  and "mono Retr2"
and "\<And> theta. Retr1 theta \<subseteq> Retr2 theta"
shows "bis Retr1 \<subseteq> bis Retr2"
by (metis assms bis_prefix bis_raw_coind subset_trans sym_bis)

end
