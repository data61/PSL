(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Semantics
  imports Weak_Early_Step_Semantics
begin

definition weakFreeTransition :: "pi \<Rightarrow> freeRes \<Rightarrow> pi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sup>^_ \<prec> _" [80, 80, 80] 80) 
  where "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P' \<equiv> P \<Longrightarrow>\<alpha> \<prec> P' \<or> (\<alpha> = \<tau> \<and> P = P')"

lemma weakTransitionI:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  shows "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and   "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P"
by(auto simp add: weakFreeTransition_def)

lemma transitionCases[consumes 1, case_names Step Stay]:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> F \<alpha> P'"
  and     "F (\<tau>) P"

  shows "F \<alpha> P'"
using assms
by(auto simp add: weakFreeTransition_def)

lemma singleActionChain:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "P \<longmapsto>\<alpha> \<prec> P'"

  shows "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
using assms
by(auto dest: singleActionChain intro: weakTransitionI)

lemma Tau:
  fixes P :: pi

  shows "\<tau>.(P) \<Longrightarrow>\<^sup>^ \<tau> \<prec>  P"
by(auto intro: Weak_Early_Step_Semantics.Tau
   simp add: weakFreeTransition_def)

lemma Input:
  fixes a :: name
  and   x :: name
  and   u :: name
  and   P :: pi

  shows "a<x>.P \<Longrightarrow>\<^sup>^ a<u> \<prec> P[x::=u]"
by(auto intro: Weak_Early_Step_Semantics.Input
   simp add: weakFreeTransition_def)
  
lemma Output:
  fixes a :: name
  and   b :: name
  and   P :: pi

  shows "a{b}.P \<Longrightarrow>\<^sup>^a[b] \<prec> P"
by(auto intro: Weak_Early_Step_Semantics.Output
   simp add: weakFreeTransition_def)

lemma Par1F:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   Q  :: pi

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> (P' \<parallel> Q)"
using assms
by(auto intro: Weak_Early_Step_Semantics.Par1F
   simp add: weakFreeTransition_def residual.inject)

lemma Par2F:
  fixes Q :: pi
  and   \<alpha>  :: freeRes
  and   Q' :: pi
  and   P  :: pi

  assumes QTrans: "Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sup>^\<alpha> \<prec> (P \<parallel> Q')"
using assms
by(auto intro: Weak_Early_Step_Semantics.Par2F
   simp add: weakFreeTransition_def residual.inject)


lemma ResF:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   x  :: name

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "x \<sharp> \<alpha>"

  shows "<\<nu>x>P \<Longrightarrow>\<^sup>^\<alpha> \<prec> <\<nu>x>P'"
using assms
by(auto intro: Weak_Early_Step_Semantics.ResF
   simp add: weakFreeTransition_def residual.inject)

lemma Bang:
  fixes P  :: pi
  and   Rs :: residual

  assumes "P \<parallel> !P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and     "P' \<noteq> P \<parallel> !P"
  
  shows "!P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
using assms
by(auto intro: Weak_Early_Step_Semantics.Bang
   simp add: weakFreeTransition_def residual.inject)

lemma tauTransitionChain[simp]:
  fixes P  :: pi
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P' = P \<Longrightarrow>\<^sub>\<tau> P'"
apply(auto dest: Weak_Early_Step_Semantics.tauTransitionChain
      simp add: weakFreeTransition_def)
by(erule rtrancl.cases) (auto intro: transitionI)

lemma tauStepTransitionChain[simp]:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<noteq> P'"

  shows "P \<Longrightarrow>\<tau> \<prec> P' = P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
apply(auto dest: Weak_Early_Step_Semantics.tauTransitionChain
      simp add: weakFreeTransition_def)
by(erule rtrancl.cases) (auto intro: transitionI)

lemma chainTransitionAppend:
  fixes P   :: pi
  and   P'  :: pi
  and   Rs  :: residual
  and   a   :: name
  and   x   :: name
  and   P'' :: pi
  and   \<alpha>   :: freeRes

  shows "P \<Longrightarrow>\<^sub>\<tau> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'  \<Longrightarrow> P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
  and   "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"
by(auto intro: chainTransitionAppend simp add: weakFreeTransition_def dest: Weak_Early_Step_Semantics.tauTransitionChain)

lemma freshTauTransition:
  fixes P :: pi
  and   c :: name

  assumes "P \<Longrightarrow>\<^sup>^\<tau> \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Early_Step_Semantics.freshTauTransition
   simp add: weakFreeTransition_def residual.inject)

lemma freshOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<Longrightarrow>\<^sup>^a[b] \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Early_Step_Semantics.freshOutputTransition
   simp add: weakFreeTransition_def residual.inject)

lemma eqvtI:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   p  :: "name prm"

  assumes "P \<Longrightarrow>\<^sup>^\<alpha> \<prec> P'"

  shows "(p \<bullet> P) \<Longrightarrow>\<^sup>^(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
using assms
by(auto intro: Weak_Early_Step_Semantics.eqvtI
   simp add: weakFreeTransition_def residual.inject)

lemma freshInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<Longrightarrow>\<^sup>^a<b> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<noteq> b"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Early_Step_Semantics.freshInputTransition
   simp add: weakFreeTransition_def residual.inject)

lemmas freshTransition = freshBoundOutputTransition freshOutputTransition
                         freshInputTransition freshTauTransition

end
