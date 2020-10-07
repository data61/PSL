(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Cong_Semantics
  imports Tau_Chain
begin

definition weakCongTrans :: "ccs \<Rightarrow> act \<Rightarrow> ccs \<Rightarrow> bool" ("_ \<Longrightarrow>_ \<prec> _" [80, 80, 80] 80)
  where "P \<Longrightarrow>\<alpha> \<prec> P' \<equiv> \<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P'' \<and> P'' \<longmapsto>\<alpha> \<prec> P''' \<and> P''' \<Longrightarrow>\<^sub>\<tau> P'"

lemma weakCongTransE:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"

  obtains P'' P''' where "P \<Longrightarrow>\<^sub>\<tau> P''" and "P'' \<longmapsto>\<alpha> \<prec> P'''" and "P''' \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(auto simp add: weakCongTrans_def)

lemma weakCongTransI:
  fixes P    :: ccs
  and   P''  :: ccs
  and   \<alpha>    :: act
  and   P''' :: ccs
  and   P'   :: ccs

  assumes "P \<Longrightarrow>\<^sub>\<tau> P''"
  and     "P'' \<longmapsto>\<alpha> \<prec> P'''"
  and     "P''' \<Longrightarrow>\<^sub>\<tau> P'"

  shows "P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(auto simp add: weakCongTrans_def)

lemma transitionWeakCongTransition:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<longmapsto>\<alpha> \<prec> P'"

  shows "P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(force simp add: weakCongTrans_def)

lemma weakCongAction:
  fixes a :: name
  and   P :: ccs

  shows "\<alpha>.(P) \<Longrightarrow>\<alpha> \<prec> P"
by(auto simp add: weakCongTrans_def)
  (blast intro: Action tauChainRefl)

lemma weakCongSum1:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> P'"
using assms
apply(auto simp add: weakCongTrans_def)
apply(case_tac "P=P''")
apply(force simp add: tauChain_def dest: Sum1)
by(force intro: tauChainSum1)

lemma weakCongSum2:
  fixes Q  :: ccs
  and   \<alpha>  :: act
  and   Q' :: ccs
  and   P  :: ccs

  assumes "Q \<Longrightarrow>\<alpha> \<prec> Q'"

  shows "P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> Q'"
using assms
apply(auto simp add: weakCongTrans_def)
apply(case_tac "Q=P''")
apply(force simp add: tauChain_def dest: Sum2)
by(force intro: tauChainSum2)

lemma weakCongPar1:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> P' \<parallel> Q"
using assms
by(auto simp add: weakCongTrans_def)
  (blast dest: tauChainPar1 Par1)

lemma weakCongPar2:
  fixes Q  :: ccs
  and   \<alpha>  :: act
  and   Q' :: ccs
  and   P  :: ccs

  assumes "Q \<Longrightarrow>\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> P \<parallel> Q'"
using assms
by(auto simp add: weakCongTrans_def)
  (blast dest: tauChainPar2 Par2)

lemma weakCongSync:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "Q \<Longrightarrow>(coAction \<alpha>) \<prec> Q'"
  and     "\<alpha> \<noteq> \<tau>"

  shows "P \<parallel> Q \<Longrightarrow>\<tau> \<prec> P' \<parallel> Q'"
using assms
apply(auto simp add: weakCongTrans_def)
apply(rule_tac x= "P'' \<parallel> P''a" in exI)
apply auto
apply(blast dest: tauChainPar1 tauChainPar2)
apply(rule_tac x="P''' \<parallel> P'''a" in exI)
apply auto
apply(rule Comm)
apply auto
apply(rule_tac P'="P' \<parallel> P'''a" in tauChainAppend)
by(blast dest: tauChainPar1 tauChainPar2)+

lemma weakCongRes:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   x  :: name

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "x \<sharp> \<alpha>"

  shows "\<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
using assms
by(auto simp add: weakCongTrans_def)
  (blast dest: tauChainRes Res)

lemma weakCongRepl:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "!P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
apply(auto simp add: weakCongTrans_def)
apply(case_tac "P'' = P \<parallel> !P")
apply auto
apply(force intro: Bang simp add: tauChain_def)
by(force intro: tauChainRepl)

end
