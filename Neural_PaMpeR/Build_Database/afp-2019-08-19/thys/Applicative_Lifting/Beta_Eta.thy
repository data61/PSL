(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Combined beta and eta reduction of lambda terms\<close>

theory Beta_Eta
imports "HOL-Proofs-Lambda.Eta" Joinable
begin

subsubsection \<open>Auxiliary lemmas\<close>

lemma liftn_lift_swap: "liftn n (lift t k) k = lift (liftn n t k) k"
by (induction n) simp_all

lemma subst_liftn:
  "i \<le> n + k \<and> k \<le> i \<Longrightarrow> (liftn (Suc n) s k)[t/i] = liftn n s k"
by (induction s arbitrary: i k t) auto

lemma subst_lift2[simp]: "(lift (lift t 0) 0)[x/Suc 0] = lift t 0"
proof -
  have "lift (lift t 0) 0 = lift (lift t 0) (Suc 0)" using lift_lift by simp
  thus ?thesis by simp
qed

lemma free_liftn:
  "free (liftn n t k) i = (i < k \<and> free t i \<or> k + n \<le> i \<and> free t (i - n))"
by (induction t arbitrary: k i) (auto simp add: Suc_diff_le)


subsubsection \<open>Reduction\<close>

abbreviation beta_eta :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>" 50)
where "beta_eta \<equiv> sup beta eta"

abbreviation beta_eta_reds :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>*" 50)
where "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<equiv> (beta_eta)\<^sup>*\<^sup>* s t"

lemma beta_into_beta_eta_reds: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by auto

lemma eta_into_beta_eta_reds: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by auto

lemma beta_reds_into_beta_eta_reds: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma eta_reds_into_beta_eta_reds: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t"
by (auto intro: rtranclp_mono[THEN predicate2D])

lemma beta_eta_appL[intro]: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s' \<degree> t"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_appR[intro]: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* s \<degree> t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_abs[intro]: "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t' \<Longrightarrow> Abs t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* Abs t'"
by (induction set: rtranclp) (auto intro: rtranclp.rtrancl_into_rtrancl)

lemma beta_eta_lift: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> lift s k \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* lift t k"
proof (induction pred: rtranclp)
  case base show ?case ..
next
  case (step y z)
  hence "lift y k \<rightarrow>\<^sub>\<beta>\<^sub>\<eta> lift z k" using lift_preserves_beta eta_lift by blast
  with step.IH show "lift s k \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* lift z k" by iprover
qed

lemma confluent_beta_eta_reds: "Joinable.confluent {(s, t). s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t}"
using confluent_beta_eta
unfolding diamond_def commute_def square_def
by (blast intro!: confluentI)


subsubsection \<open>Equivalence\<close>

text \<open>Terms are equivalent iff they can be reduced to a common term.\<close>

definition term_equiv :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<leftrightarrow>" 50)
where "term_equiv = joinablep beta_eta_reds"

lemma term_equivI:
  assumes "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" and "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u"
  shows "s \<leftrightarrow> t"
using assms unfolding term_equiv_def by (rule joinableI[to_pred])

lemma term_equivE:
  assumes "s \<leftrightarrow> t"
  obtains u where "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u" and "t \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* u"
using assms unfolding term_equiv_def by (rule joinableE[to_pred])

lemma reds_into_equiv[elim]: "s \<rightarrow>\<^sub>\<beta>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<leftrightarrow> t"
by (blast intro: term_equivI)

lemma beta_into_equiv[elim]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> s \<leftrightarrow> t"
by (rule reds_into_equiv) (rule beta_into_beta_eta_reds)

lemma eta_into_equiv[elim]: "s \<rightarrow>\<^sub>\<eta> t \<Longrightarrow> s \<leftrightarrow> t"
by (rule reds_into_equiv) (rule eta_into_beta_eta_reds)

lemma beta_reds_into_equiv[elim]: "s \<rightarrow>\<^sub>\<beta>\<^sup>* t \<Longrightarrow> s \<leftrightarrow> t"
by (rule reds_into_equiv) (rule beta_reds_into_beta_eta_reds)

lemma eta_reds_into_equiv[elim]: "s \<rightarrow>\<^sub>\<eta>\<^sup>* t \<Longrightarrow> s \<leftrightarrow> t"
by (rule reds_into_equiv) (rule eta_reds_into_beta_eta_reds)

lemma term_refl[iff]: "t \<leftrightarrow> t"
unfolding term_equiv_def by (blast intro: joinablep_refl reflpI)

lemma term_sym[sym]: "(s \<leftrightarrow> t) \<Longrightarrow> (t \<leftrightarrow> s)"
unfolding term_equiv_def by (rule joinable_sym[to_pred])

lemma conversep_term [simp]: "conversep (\<leftrightarrow>) = (\<leftrightarrow>)"
by (auto simp add: fun_eq_iff intro: term_sym)

lemma term_trans[trans]: "s \<leftrightarrow> t \<Longrightarrow> t \<leftrightarrow> u \<Longrightarrow> s \<leftrightarrow> u"
unfolding term_equiv_def
using trans_joinable[to_pred] trans_rtrancl[to_pred] confluent_beta_eta_reds
by (blast elim: transpE)

lemma term_beta_trans[trans]: "s \<leftrightarrow> t \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> u \<Longrightarrow> s \<leftrightarrow> u"
by (fast dest!: beta_into_beta_eta_reds intro: term_trans)

lemma term_eta_trans[trans]: "s \<leftrightarrow> t \<Longrightarrow> t \<rightarrow>\<^sub>\<eta> u \<Longrightarrow> s \<leftrightarrow> u"
by (fast dest!: eta_into_beta_eta_reds intro: term_trans)

lemma equiv_appL[intro]: "s \<leftrightarrow> s' \<Longrightarrow> s \<degree> t \<leftrightarrow> s' \<degree> t"
unfolding term_equiv_def using beta_eta_appL
by (iprover intro: joinable_subst[to_pred])

lemma equiv_appR[intro]: "t \<leftrightarrow> t' \<Longrightarrow> s \<degree> t \<leftrightarrow> s \<degree> t'"
unfolding term_equiv_def using beta_eta_appR
by (iprover intro: joinable_subst[to_pred])

lemma equiv_app: "s \<leftrightarrow> s' \<Longrightarrow> t \<leftrightarrow> t' \<Longrightarrow> s \<degree> t \<leftrightarrow> s' \<degree> t'"
by (blast intro: term_trans)

lemma equiv_abs[intro]: "t \<leftrightarrow> t' \<Longrightarrow> Abs t \<leftrightarrow> Abs t'"
unfolding term_equiv_def using beta_eta_abs
by (iprover intro: joinable_subst[to_pred])

lemma equiv_lift: "s \<leftrightarrow> t \<Longrightarrow> lift s k \<leftrightarrow> lift t k"
by (auto intro: term_equivI beta_eta_lift elim: term_equivE)

lemma equiv_liftn: "s \<leftrightarrow> t \<Longrightarrow> liftn n s k \<leftrightarrow> liftn n t k"
by (induction n) (auto intro: equiv_lift)

text \<open>Our definition is equivalent to the the symmetric and transitive closure of
  the reduction relation.\<close>

lemma equiv_eq_rtscl_reds: "term_equiv = (sup beta_eta beta_eta\<inverse>\<inverse>)\<^sup>*\<^sup>*"
unfolding term_equiv_def
using confluent_beta_eta_reds
by (rule joinable_eq_rtscl[to_pred])

end
