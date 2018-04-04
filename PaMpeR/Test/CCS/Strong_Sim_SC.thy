(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Strong_Sim_SC
  imports Strong_Sim
begin

lemma resNilLeft:
  fixes x :: name

  shows "\<lparr>\<nu>x\<rparr>\<zero> \<leadsto>[Rel] \<zero>"
by(auto simp add: simulation_def)

lemma resNilRight:
  fixes x :: name

  shows "\<zero> \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>\<zero>"
by(auto simp add: simulation_def elim: resCases)

lemma test[simp]:
  fixes x :: name
  and   P :: ccs

  shows "x \<sharp> [x].P"
by(auto simp add: abs_fresh)

lemma scopeExtSumLeft:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"
  and     C1: "\<And>y R. y \<sharp> R \<Longrightarrow> (\<lparr>\<nu>y\<rparr>R, R) \<in> Rel"
  and     "Id \<subseteq> Rel"

  shows "\<lparr>\<nu>x\<rparr>(P \<oplus> Q) \<leadsto>[Rel] P \<oplus> \<lparr>\<nu>x\<rparr>Q"
using assms
apply(auto simp add: simulation_def)
by(elim sumCases resCases) (blast intro: Res Sum1 Sum2 C1 dest: freshDerivative)+

lemma scopeExtSumRight:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"
  and     C1: "\<And>y R. y \<sharp> R \<Longrightarrow> (R, \<lparr>\<nu>y\<rparr>R) \<in> Rel"
  and     "Id \<subseteq> Rel"

  shows "P \<oplus> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<oplus> Q)"
using assms
apply(auto simp add: simulation_def)
by(elim sumCases resCases) (blast intro: Res Sum1 Sum2 C1 dest: freshDerivative)+

lemma scopeExtLeft:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"
  and     C1: "\<And>y R T. y \<sharp> R \<Longrightarrow> (\<lparr>\<nu>y\<rparr>(R \<parallel> T), R \<parallel> \<lparr>\<nu>y\<rparr>T) \<in> Rel"

  shows "\<lparr>\<nu>x\<rparr>(P \<parallel> Q) \<leadsto>[Rel] P \<parallel> \<lparr>\<nu>x\<rparr>Q"
using assms
by(fastforce elim: parCases resCases intro: Res C1 Par1 Par2 Comm dest: freshDerivative simp add: simulation_def)

lemma scopeExtRight:
  fixes x :: name
  and   P :: ccs
  and   Q :: ccs

  assumes "x \<sharp> P"
  and     C1: "\<And>y R T. y \<sharp> R \<Longrightarrow> (R \<parallel> \<lparr>\<nu>y\<rparr>T, \<lparr>\<nu>y\<rparr>(R \<parallel> T)) \<in> Rel"

  shows "P \<parallel> \<lparr>\<nu>x\<rparr>Q \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(P \<parallel> Q)"
using assms
by(fastforce elim: parCases resCases intro: Res C1 Par1 Par2 Comm dest: freshDerivative simp add: simulation_def)

lemma sumComm:
  fixes P :: ccs
  and   Q :: ccs

  assumes "Id \<subseteq> Rel"

  shows "P \<oplus> Q \<leadsto>[Rel] Q \<oplus> P"
using assms
by(force simp add: simulation_def elim: sumCases intro: Sum1 Sum2)

lemma sumAssocLeft:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "Id \<subseteq> Rel"

  shows "(P \<oplus> Q) \<oplus> R \<leadsto>[Rel] P \<oplus> (Q \<oplus> R)"
using assms
by(force simp add: simulation_def elim: sumCases intro: Sum1 Sum2)

lemma sumAssocRight:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes "Id \<subseteq> Rel"

  shows " P \<oplus> (Q \<oplus> R) \<leadsto>[Rel] (P \<oplus> Q) \<oplus> R"
using assms
by(intro simI, elim sumCases) (blast intro: Sum1 Sum2)+

lemma sumIdLeft:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "Id \<subseteq> Rel"

  shows "P \<oplus> \<zero> \<leadsto>[Rel] P"
using assms
by(auto simp add: simulation_def intro: Sum1)

lemma sumIdRight:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P \<oplus> \<zero>"
using assms
by(fastforce simp add: simulation_def elim: sumCases)

lemma parComm:
  fixes P :: ccs
  and   Q :: ccs

  assumes C1: "\<And>R T. (R \<parallel> T, T \<parallel> R) \<in> Rel"

  shows "P \<parallel> Q \<leadsto>[Rel] Q \<parallel> P"
by(fastforce simp add: simulation_def elim: parCases intro: Par1 Par2 Comm C1)

lemma parAssocLeft:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes C1: "\<And>S T U. ((S \<parallel> T) \<parallel> U, S \<parallel> (T \<parallel> U)) \<in> Rel"

  shows "(P \<parallel> Q) \<parallel> R \<leadsto>[Rel] P \<parallel> (Q \<parallel> R)"
by(fastforce simp add: simulation_def elim: parCases intro: Par1 Par2 Comm C1)

lemma parAssocRight:
  fixes P :: ccs
  and   Q :: ccs
  and   R :: ccs

  assumes C1: "\<And>S T U. (S \<parallel> (T \<parallel> U), (S \<parallel> T) \<parallel> U) \<in> Rel"

  shows "P \<parallel> (Q \<parallel> R) \<leadsto>[Rel] (P \<parallel> Q) \<parallel> R"
by(fastforce simp add: simulation_def elim: parCases intro: Par1 Par2 Comm C1)

lemma parIdLeft:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "\<And>Q. (Q \<parallel> \<zero>, Q) \<in> Rel"

  shows "P \<parallel> \<zero> \<leadsto>[Rel] P"
using assms
by(auto simp add: simulation_def intro: Par1)

lemma parIdRight:
  fixes P   :: ccs
  and   Rel :: "(ccs \<times> ccs) set"
  
  assumes "\<And>Q. (Q, Q \<parallel> \<zero>) \<in> Rel"

  shows "P \<leadsto>[Rel] P \<parallel> \<zero>"
using assms
by(fastforce simp add: simulation_def elim: parCases)

declare fresh_atm[simp]

lemma resActLeft:
  fixes x :: name
  and   \<alpha> :: act
  and   P :: ccs

  assumes "x \<sharp> \<alpha>"
  and     "Id \<subseteq> Rel"

  shows "\<lparr>\<nu>x\<rparr>(\<alpha>.(P)) \<leadsto>[Rel] (\<alpha>.(\<lparr>\<nu>x\<rparr>P))"
using assms
by(fastforce simp add: simulation_def elim: actCases intro: Res Action) 

lemma resActRight:
  fixes x :: name
  and   \<alpha> :: act
  and   P :: ccs

  assumes "x \<sharp> \<alpha>"
  and     "Id \<subseteq> Rel"

  shows "\<alpha>.(\<lparr>\<nu>x\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>x\<rparr>(\<alpha>.(P))"
using assms
by(fastforce simp add: simulation_def elim: resCases actCases intro: Action) 

lemma resComm:
  fixes x :: name
  and   y :: name 
  and   P :: ccs

  assumes "\<And>Q. (\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>Q), \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>Q)) \<in> Rel"

  shows "\<lparr>\<nu>x\<rparr>(\<lparr>\<nu>y\<rparr>P) \<leadsto>[Rel] \<lparr>\<nu>y\<rparr>(\<lparr>\<nu>x\<rparr>P)"
using assms
by(fastforce simp add: simulation_def elim: resCases intro: Res)

inductive_cases bangCases[simplified ccs.distinct act.distinct]: "!P \<longmapsto>\<alpha> \<prec> P'"

lemma bangUnfoldLeft:
  fixes P :: ccs
  
  assumes "Id \<subseteq> Rel"

  shows "P \<parallel> !P \<leadsto>[Rel] !P"
using assms
by(fastforce simp add: simulation_def ccs.inject elim: bangCases)

lemma bangUnfoldRight:
  fixes P :: ccs
  
  assumes "Id \<subseteq> Rel"

  shows "!P \<leadsto>[Rel] P \<parallel> !P"
using assms
by(fastforce simp add: simulation_def ccs.inject intro: Bang)

end 

