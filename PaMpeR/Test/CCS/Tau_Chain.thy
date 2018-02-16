(* 
   Title: The Calculus of Communicating Systems   
   Author/Maintainer: Jesper Bengtson (jebe@itu.dk), 2012
*)
theory Tau_Chain
  imports Agent
begin


definition tauChain :: "ccs \<Rightarrow> ccs \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>\<tau> _" [80, 80] 80)
  where "P \<Longrightarrow>\<^sub>\<tau> P' \<equiv> (P, P') \<in> {(P, P') | P P'. P \<longmapsto>\<tau> \<prec> P'}^*"

lemma tauChainInduct[consumes 1, case_names Base Step]:
  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "Prop P"
  and     "\<And>P' P''. \<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'; P' \<longmapsto>\<tau> \<prec> P''; Prop P'\<rbrakk> \<Longrightarrow> Prop P''"

  shows "Prop P'"
using assms
by(auto simp add: tauChain_def elim: rtrancl_induct)

lemma tauChainRefl[simp]:
  fixes P :: ccs

  shows "P \<Longrightarrow>\<^sub>\<tau> P"
by(auto simp add: tauChain_def)

lemma tauChainCons[dest]:
  fixes P   :: ccs
  and   P'  :: ccs
  and   P'' :: ccs

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "P' \<longmapsto>\<tau> \<prec> P''"

  shows "P \<Longrightarrow>\<^sub>\<tau> P''"
using assms
by(auto simp add: tauChain_def) (blast dest: rtrancl_trans)

lemma tauChainCons2[dest]:
  fixes P   :: ccs
  and   P'  :: ccs
  and   P'' :: ccs

  assumes "P' \<longmapsto>\<tau> \<prec> P''"
  and     "P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "P \<Longrightarrow>\<^sub>\<tau> P''"
using assms
by(auto simp add: tauChain_def) (blast dest: rtrancl_trans)

lemma tauChainAppend[dest]:
  fixes P   :: ccs
  and   P'  :: ccs
  and   P'' :: ccs

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "P' \<Longrightarrow>\<^sub>\<tau> P''"

  shows "P \<Longrightarrow>\<^sub>\<tau> P''"
using `P' \<Longrightarrow>\<^sub>\<tau> P''` `P \<Longrightarrow>\<^sub>\<tau> P'`
by(induct rule: tauChainInduct) auto

lemma tauChainSum1:
  fixes P  :: ccs
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "P \<noteq> P'"

  shows "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P'"
using assms
proof(induct rule: tauChainInduct)
  case Base 
  thus ?case by simp
next
  case(Step P' P'')
  thus ?case
    by(case_tac "P=P'") (auto intro: Sum1 simp add: tauChain_def)
qed

lemma tauChainSum2:
  fixes P  :: ccs
  and   P' :: ccs
  and   Q  :: ccs

  assumes "Q \<Longrightarrow>\<^sub>\<tau> Q'"
  and     "Q \<noteq> Q'"

  shows "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q'"
using assms
proof(induct rule: tauChainInduct)
  case Base 
  thus ?case by simp
next
  case(Step Q' Q'')
  thus ?case
    by(case_tac "Q=Q'") (auto intro: Sum2 simp add: tauChain_def)
qed

lemma tauChainPar1:
  fixes P  :: ccs
  and   P' :: ccs
  and   Q  :: ccs

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q"
using assms
by(induct rule: tauChainInduct) (auto intro: Par1)

lemma tauChainPar2:
  fixes Q  :: ccs
  and   Q' :: ccs
  and   P  :: ccs

  assumes "Q \<Longrightarrow>\<^sub>\<tau> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'"
using assms
by(induct rule: tauChainInduct) (auto intro: Par2)

lemma tauChainRes:
  fixes P  :: ccs
  and   P' :: ccs
  and   x  :: name

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "\<lparr>\<nu>x\<rparr>P \<Longrightarrow>\<^sub>\<tau> \<lparr>\<nu>x\<rparr>P'"
using assms
by(induct rule: tauChainInduct) (auto dest: Res)

lemma tauChainRepl:
  fixes P :: ccs

  assumes "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'"
  and     "P' \<noteq> P \<parallel> !P"

  shows "!P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
apply(induct rule: tauChainInduct)
apply auto
apply(case_tac "P' \<noteq> P \<parallel> !P")
apply auto
apply(drule Bang)
apply(simp add: tauChain_def)
by auto

end
