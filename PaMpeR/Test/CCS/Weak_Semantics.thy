(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Weak_Semantics
  imports Weak_Cong_Semantics
begin

definition weakTrans :: "ccs \<Rightarrow> act \<Rightarrow> ccs \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sup>^_ \<prec> _" [80, 80, 80] 80)
  where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<equiv> P \<Longrightarrow>\<alpha> \<prec> P' \<or> (\<alpha> = \<tau> \<and> P = P')"

lemma weakEmptyTrans[simp]:
  fixes P :: ccs

  shows "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P"
by(auto simp add: weakTrans_def)

lemma weakTransCases[consumes 1, case_names Base Step]:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "\<lbrakk>\<alpha> = \<tau>; P = P'\<rbrakk> \<Longrightarrow> Prop (\<tau>) P"
  and     "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> Prop \<alpha> P'"

  shows "Prop \<alpha> P'"
using assms
by(auto simp add: weakTrans_def)

lemma weakCongTransitionWeakTransition:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTrans_def)

lemma transitionWeakTransition:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<longmapsto>\<alpha> \<prec> P'"

  shows "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
using assms
by(auto dest: transitionWeakCongTransition weakCongTransitionWeakTransition)

lemma weakAction:
  fixes a :: name
  and   P :: ccs

  shows "\<alpha>.(P) \<Longrightarrow>\<^sup>^\<alpha> \<prec> P"
by(auto simp add: weakTrans_def intro: weakCongAction)

lemma weakSum1:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "P \<noteq> P'"

  shows "P \<oplus> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTrans_def intro: weakCongSum1)

lemma weakSum2:
  fixes Q  :: ccs
  and   \<alpha>  :: act
  and   Q' :: ccs
  and   P  :: ccs

  assumes "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"
  and     "Q \<noteq> Q'"

  shows "P \<oplus> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"
using assms
by(auto simp add: weakTrans_def intro: weakCongSum2)

lemma weakPar1:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<parallel> Q"
using assms
by(auto simp add: weakTrans_def intro: weakCongPar1)

lemma weakPar2:
  fixes Q  :: ccs
  and   \<alpha>  :: act
  and   Q' :: ccs
  and   P  :: ccs

  assumes "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> P \<parallel> Q'"
using assms
by(auto simp add: weakTrans_def intro: weakCongPar2)

lemma weakSync:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "Q \<Longrightarrow>\<^sup>^(coAction \<alpha>) \<prec> Q'"
  and     "\<alpha> \<noteq> \<tau>"

  shows "P \<parallel> Q \<Longrightarrow>\<^sup>^\<tau> \<prec> P' \<parallel> Q'"
using assms
by(auto simp add: weakTrans_def intro: weakCongSync)

lemma weakRes:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs
  and   x  :: name

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "x \<sharp> \<alpha>"

  shows "\<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> \<lparr>\<nu>x\<rparr>P'"
using assms
by(auto simp add: weakTrans_def intro: weakCongRes)

lemma weakRepl:
  fixes P  :: ccs
  and   \<alpha>  :: act
  and   P' :: ccs

  assumes "P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "P' \<noteq> P \<parallel> !P"

  shows "!P \<Longrightarrow>\<alpha> \<prec> P'"
using assms
by(auto simp add: weakTrans_def intro: weakCongRepl)

end
