(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Semantics
  imports Weak_Late_Step_Semantics
begin

definition weakTransition :: "(pi \<times> residual) set"
  where "weakTransition \<equiv> Weak_Late_Step_Semantics.transition \<union> {x. \<exists>P. x = (P, \<tau> \<prec> P)}"

abbreviation weakLateTransition_judge :: "pi \<Rightarrow> residual \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>l\<^sup>^_" [80, 80] 80)
  where "P \<Longrightarrow>\<^sub>l\<^sup>^Rs \<equiv> (P, Rs) \<in> weakTransition"

lemma transitionI:
  fixes P  :: pi
  and   Rs :: residual
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<^sup>^Rs"
  and   "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P"
proof -
  assume "P \<Longrightarrow>\<^sub>l Rs"
  thus "P \<Longrightarrow>\<^sub>l\<^sup>^Rs" by(simp add: weakTransition_def)
next
  show "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P" by(simp add: weakTransition_def)
qed

lemma transitionCases[consumes 1, case_names Step Stay]:
  fixes P  :: pi
  and   Rs :: residual
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
  and     "P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> F Rs"
  and     "Rs = \<tau> \<prec> P \<Longrightarrow> F (\<tau> \<prec> P)"

  shows "F Rs"
using assms
by(auto simp add: weakTransition_def)

lemma singleActionChain:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  
  assumes "P \<longmapsto>\<alpha> \<prec> P'"
  
  shows "P \<Longrightarrow>\<^sub>l\<^sup>^(\<alpha> \<prec> P')"
using assms
by(auto intro: Weak_Late_Step_Semantics.singleActionChain
  simp add: weakTransition_def)

lemma Tau:
  fixes P :: pi

  shows "\<tau>.(P) \<Longrightarrow>\<^sub>l\<^sup>^ \<tau> \<prec>  P"
by(auto intro: Weak_Late_Step_Semantics.Tau
   simp add: weakTransition_def)
  
lemma Output:
  fixes a :: name
  and   b :: name
  and   P :: pi

  shows "a{b}.P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P"
by(auto intro: Weak_Late_Step_Semantics.Output
   simp add: weakTransition_def)

lemma Match:
  fixes a  :: name
  and   P  :: pi
  and   b  :: name
  and   x  :: name
  and   P' :: pi
  and   \<alpha>  :: freeRes

  shows "P \<Longrightarrow>\<^sub>l\<^sup>^b<\<nu>x> \<prec> P' \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>\<^sub>l\<^sup>^b<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P' \<Longrightarrow> P \<noteq> P' \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
by(auto simp add: residual.inject weakTransition_def intro: Weak_Late_Step_Semantics.Match)

lemma Mismatch:
  fixes a  :: name
  and   c  :: name
  and   P  :: pi
  and   b  :: name
  and   x  :: name
  and   P' :: pi
  and   \<alpha>  :: freeRes

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>l\<^sup>^b<\<nu>x> \<prec> P'; a \<noteq> c\<rbrakk> \<Longrightarrow> [a\<noteq>c]P \<Longrightarrow>\<^sub>l\<^sup>^b<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P' \<Longrightarrow> P \<noteq> P' \<Longrightarrow> a \<noteq> c \<Longrightarrow> [a\<noteq>c]P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
by(auto simp add: residual.inject weakTransition_def intro: Weak_Late_Step_Semantics.Mismatch)

lemma Open:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes Trans:  "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'"
  and     aInEqb: "a \<noteq> b"

  shows "<\<nu>b>P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>b> \<prec> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.Open
  simp add: weakTransition_def residual.inject)

lemma Par1B:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
  and     xFreshQ: "x \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> (P' \<parallel> Q)"
using assms
by(auto intro: Weak_Late_Step_Semantics.Par1B
  simp add: weakTransition_def residual.inject)

lemma Par1F:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> (P' \<parallel> Q)"
using assms
by(auto intro: Weak_Late_Step_Semantics.Par1F
  simp add: weakTransition_def residual.inject)

lemma Par2B:
  fixes Q  :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi

  assumes QTrans: "Q \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> Q'"
  and     xFreshP: "x \<sharp> P"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> (P \<parallel> Q')"
using assms
by(auto intro: Weak_Late_Step_Semantics.Par2B
  simp add: weakTransition_def residual.inject)

lemma Par2F:
  fixes Q :: pi
  and   \<alpha>  :: freeRes
  and   Q' :: pi

  assumes QTrans: "Q \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> (P \<parallel> Q')"
using assms
by(auto intro: Weak_Late_Step_Semantics.Par2F
  simp add: weakTransition_def residual.inject)

lemma Comm1:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P'' :: pi
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>lb in P''\<rightarrow>a<x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P' \<parallel> Q'"
using assms
by(auto intro: Weak_Late_Step_Semantics.Comm1
  simp add: weakTransition_def residual.inject)

lemma Comm2:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   Q'' :: pi
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>lb in Q''\<rightarrow>a<x> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P' \<parallel> Q'"
using assms
by(auto intro: Weak_Late_Step_Semantics.Comm2
  simp add: weakTransition_def residual.inject)

lemma Close1:
  fixes P  :: pi
  and   y  :: name
  and   P'' :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>ly in P''\<rightarrow>a<x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> Q'"
  and     xFreshP: "y \<sharp> P"
  and     xFreshQ: "y \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')"
using assms
by(auto intro: Weak_Late_Step_Semantics.Close1
  simp add: weakTransition_def residual.inject)

lemma Close2:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   y  :: name
  and   Q'' :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>y> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>ly in Q''\<rightarrow>a<x> \<prec> Q'"
  and     xFreshP: "y \<sharp> P"
  and     xFreshQ: "y \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')"
using assms
by(auto intro: Weak_Late_Step_Semantics.Close2
  simp add: weakTransition_def residual.inject)

lemma ResF:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   x  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
  and     xFreshAlpha: "x \<sharp> \<alpha>"

  shows "<\<nu>x>P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> <\<nu>x>P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.ResF
  simp add: weakTransition_def residual.inject)

lemma ResB:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   y  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
  and     yineqa: "y \<noteq> a"
  and     yineqx: "y \<noteq> x"
  and     xFreshP: "x \<sharp> P"

  shows "<\<nu>y>P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> (<\<nu>y>P')"
using assms
by(auto intro: Weak_Late_Step_Semantics.ResB
  simp add: weakTransition_def residual.inject)

lemma Bang:
  fixes P  :: pi
  and   Rs :: residual

  assumes "P \<parallel> !P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
  and     "Rs \<noteq> \<tau> \<prec> P \<parallel> !P"
  
  shows "!P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
using assms
by(auto intro: Weak_Late_Step_Semantics.Bang
  simp add: weakTransition_def residual.inject)

lemma tauTransitionChain:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.tauTransitionChain
  simp add: weakTransition_def residual.inject transition_def)
  
lemma chainTransitionAppend:
  fixes P   :: pi
  and   P'  :: pi
  and   Rs  :: residual
  and   a   :: name
  and   x   :: name
  and   P'' :: pi
  and   \<alpha>   :: freeRes

  shows "P \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P' \<Longrightarrow>\<^sub>l\<^sup>^ Rs \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
  and   "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> x \<sharp> P \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>\<tau> P'" and "P' \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
  thus "P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"
    by(auto intro: Weak_Late_Step_Semantics.chainTransitionAppend
                   Weak_Late_Step_Semantics.tauActionChain
       simp add: weakTransition_def residual.inject)
next
  assume "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P''" and "P'' \<Longrightarrow>\<^sub>\<tau> P'" and "x \<sharp> P"
  thus "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
    by(auto intro: Weak_Late_Step_Semantics.chainTransitionAppend
       simp add: weakTransition_def residual.inject)
next
  assume "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P''" and "P'' \<Longrightarrow>\<^sub>\<tau> P'"
  thus "P \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P'"
    apply(case_tac "P''=P'")
    by(auto dest: Weak_Late_Step_Semantics.chainTransitionAppend
                     Weak_Late_Step_Semantics.tauActionChain
       simp add: weakTransition_def residual.inject)
qed

lemma weakEqWeakTransitionAppend:
  fixes P   :: pi
  and   P'  :: pi
  and   \<alpha>   :: freeRes
  and   P'' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
  and     P'Trans: "P' \<Longrightarrow>\<^sub>l\<^sup>^\<alpha> \<prec> P''"
  
  shows "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P''"
proof(cases "\<alpha>=\<tau>")
  assume alphaEqTau: "\<alpha> = \<tau>"
  with P'Trans have "P' \<Longrightarrow>\<^sub>\<tau> P''" by(blast intro: tauTransitionChain)
  with PTrans alphaEqTau show ?thesis
    by(blast intro: Weak_Late_Step_Semantics.chainTransitionAppend)
next
  assume alphaIneqTau: "\<alpha> \<noteq> \<tau>"
  from PTrans have "P \<Longrightarrow>\<^sub>\<tau> P'" by(rule Weak_Late_Step_Semantics.tauTransitionChain)
  moreover from P'Trans alphaIneqTau have "P' \<Longrightarrow>\<^sub>l\<alpha> \<prec> P''"
    by(auto simp add: weakTransition_def residual.inject)
  ultimately show ?thesis
    by(rule Weak_Late_Step_Semantics.chainTransitionAppend)
qed
    
lemma freshBoundOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<\<nu>x> \<prec> P'"
  and     cFreshP: "c \<sharp> P"
  and     cineqx: "c \<noteq> x"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.freshBoundOutputTransition
  simp add: weakTransition_def residual.inject)

lemma freshTauTransition:
  fixes P :: pi
  and   c :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^\<tau> \<prec> P'"
  and     cFreshP: "c \<sharp> P"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.freshTauTransition
  simp add: weakTransition_def residual.inject)

lemma freshOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a[b] \<prec> P'"
  and     cFreshP: "c \<sharp> P"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.freshOutputTransition
  simp add: weakTransition_def residual.inject)

lemma eqvtI:
  fixes P    :: pi
  and   Rs   :: residual
  and   perm :: "name prm"

  assumes "P \<Longrightarrow>\<^sub>l\<^sup>^ Rs"

  shows "(perm \<bullet> P) \<Longrightarrow>\<^sub>l\<^sup>^ (perm \<bullet> Rs)"
using assms
by(auto intro: Weak_Late_Step_Semantics.eqvtI
  simp add: weakTransition_def residual.inject)

lemma freshInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<^sup>^a<b> \<prec> P'"
  and     cFreshP: "c \<sharp> P"
  and     cineqb: "c \<noteq> b"

  shows "c \<sharp> P'"
using assms
by(auto intro: Weak_Late_Step_Semantics.freshInputTransition
  simp add: weakTransition_def residual.inject)

lemmas freshTransition = freshBoundOutputTransition freshOutputTransition
                         freshInputTransition freshTauTransition

end
