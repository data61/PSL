theory Residual
imports
  Nominal2.Nominal2
begin

section \<open>Residuals\<close>

subsection \<open>Binding names\<close>

text \<open>To define $\alpha$-equivalence, we require actions to be equipped with an equivariant
function~@{term bn} that gives their binding names. Actions may only bind finitely many names. This
is necessary to ensure that we can use a finite permutation to rename the binding names in an
action.\<close>

class bn = fs +
  fixes bn :: "'a \<Rightarrow> atom set"
  assumes bn_eqvt: "p \<bullet> (bn \<alpha>) = bn (p \<bullet> \<alpha>)"
  and bn_finite: "finite (bn \<alpha>)"

lemma bn_subset_supp: "bn \<alpha> \<subseteq> supp \<alpha>"
by (metis (erased, hide_lams) bn_eqvt bn_finite eqvt_at_def finite_supp supp_eqvt_at supp_finite_atom_set)


subsection \<open>Raw residuals and \texorpdfstring{$\alpha$}{alpha}-equivalence\<close>

text \<open>Raw residuals are simply pairs of actions and states. Binding names in the action bind into
(the action and) the state.\<close>

fun alpha_residual :: "('act::bn \<times> 'state::pt) \<Rightarrow> ('act \<times> 'state) \<Rightarrow> bool" where
  "alpha_residual (\<alpha>1,P1) (\<alpha>2,P2) \<longleftrightarrow> [bn \<alpha>1]set. (\<alpha>1, P1) = [bn \<alpha>2]set. (\<alpha>2, P2)"

text \<open>$\alpha$-equivalence is equivariant.\<close>

lemma alpha_residual_eqvt [eqvt]:
  assumes "alpha_residual r1 r2"
  shows "alpha_residual (p \<bullet> r1) (p \<bullet> r2)"
using assms by (cases r1, cases r2) (simp, metis Pair_eqvt bn_eqvt permute_Abs_set)

text \<open>$\alpha$-equivalence is an equivalence relation.\<close>

lemma alpha_residual_reflp: "reflp alpha_residual"
by (metis alpha_residual.simps prod.exhaust reflpI)

lemma alpha_residual_symp: "symp alpha_residual"
by (metis alpha_residual.simps prod.exhaust sympI)

lemma alpha_residual_transp: "transp alpha_residual"
by (rule transpI) (metis alpha_residual.simps prod.exhaust)

lemma alpha_residual_equivp: "equivp alpha_residual"
by (metis alpha_residual_reflp alpha_residual_symp alpha_residual_transp equivpI)


subsection \<open>Residuals\<close>

text \<open>Residuals are raw residuals quotiented by $\alpha$-equivalence.\<close>

quotient_type
  ('act,'state) residual = "'act::bn \<times> 'state::pt" / "alpha_residual"
  by (fact alpha_residual_equivp)

lemma residual_abs_rep [simp]: "abs_residual (rep_residual res) = res"
by (metis Quotient_residual Quotient_abs_rep)

lemma residual_rep_abs [simp]: "alpha_residual (rep_residual (abs_residual r)) r"
by (metis residual.abs_eq_iff residual_abs_rep)

text \<open>The permutation operation is lifted from raw residuals.\<close>

instantiation residual :: (bn,pt) pt
begin

  lift_definition permute_residual :: "perm \<Rightarrow> ('a,'b) residual \<Rightarrow> ('a,'b) residual"
    is permute
  by (fact alpha_residual_eqvt)

  instance
  proof
    fix res :: "(_,_) residual"
    show "0 \<bullet> res = res"
      by transfer (metis alpha_residual_equivp equivp_reflp permute_zero)
  next
    fix p q :: perm and res :: "(_,_) residual"
    show "(p + q) \<bullet> res = p \<bullet> q \<bullet> res"
      by transfer (metis alpha_residual_equivp equivp_reflp permute_plus)
  qed

end

text \<open>The abstraction function from raw residuals to residuals is equivariant. The representation
function is equivariant modulo $\alpha$-equivalence.\<close>

lemmas permute_residual.abs_eq [eqvt, simp]

lemma alpha_residual_permute_rep_commute [simp]: "alpha_residual (p \<bullet> rep_residual res) (rep_residual (p \<bullet> res))"
by (metis residual.abs_eq_iff residual_abs_rep permute_residual.abs_eq)


subsection \<open>Notation for pairs as residuals\<close>

abbreviation abs_residual_pair :: "'act::bn \<Rightarrow> 'state::pt \<Rightarrow> ('act,'state) residual" ("\<langle>_,_\<rangle>" [0,0] 1000)
where
  "\<langle>\<alpha>,P\<rangle> == abs_residual (\<alpha>,P)"

lemma abs_residual_pair_eqvt [simp]: "p \<bullet> \<langle>\<alpha>,P\<rangle> = \<langle>p \<bullet> \<alpha>, p \<bullet> P\<rangle>"
by (metis Pair_eqvt permute_residual.abs_eq)


subsection \<open>Support of residuals\<close>

text \<open>We only consider finitely supported states now.\<close>

lemma supp_abs_residual_pair: "supp \<langle>\<alpha>, P::'state::fs\<rangle> = supp (\<alpha>,P) - bn \<alpha>"
proof -
  have "supp \<langle>\<alpha>,P\<rangle> = supp ([bn \<alpha>]set. (\<alpha>, P))"
    by (simp add: supp_def residual.abs_eq_iff bn_eqvt)
  then show ?thesis by (simp add: supp_Abs)
qed

lemma bn_abs_residual_fresh [simp]: "bn \<alpha> \<sharp>* \<langle>\<alpha>,P::'state::fs\<rangle>"
by (simp add: fresh_star_def fresh_def supp_abs_residual_pair)

lemma finite_supp_abs_residual_pair [simp]: "finite (supp \<langle>\<alpha>, P::'state::fs\<rangle>)"
by (metis finite_Diff finite_supp supp_abs_residual_pair)


subsection \<open>Equality between residuals\<close>

lemma residual_eq_iff_perm: "\<langle>\<alpha>1,P1\<rangle> = \<langle>\<alpha>2,P2\<rangle> \<longleftrightarrow>
  (\<exists>p. supp (\<alpha>1, P1) - bn \<alpha>1 = supp (\<alpha>2, P2) - bn \<alpha>2 \<and> (supp (\<alpha>1, P1) - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> (\<alpha>1, P1) = (\<alpha>2, P2) \<and> p \<bullet> bn \<alpha>1 = bn \<alpha>2)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume *: "?l"
  then have "[bn \<alpha>1]set. (\<alpha>1, P1) = [bn \<alpha>2]set. (\<alpha>2, P2)"
    by (simp add: residual.abs_eq_iff)
  then obtain p where "(bn \<alpha>1, (\<alpha>1,P1)) \<approx>set ((=)) supp p (bn \<alpha>2, (\<alpha>2,P2))"
    using Abs_eq_iff(1) by blast
  then show "?r"
    by (metis (mono_tags, lifting) alpha_set.simps)
next
  assume *: "?r"
  then obtain p where "(bn \<alpha>1, (\<alpha>1,P1)) \<approx>set ((=)) supp p (bn \<alpha>2, (\<alpha>2,P2))"
    using alpha_set.simps by blast
  then have "[bn \<alpha>1]set. (\<alpha>1, P1) = [bn \<alpha>2]set. (\<alpha>2, P2)"
    using Abs_eq_iff(1) by blast
  then show "?l"
    by (simp add: residual.abs_eq_iff)
qed

lemma residual_eq_iff_perm_renaming: "\<langle>\<alpha>1,P1\<rangle> = \<langle>\<alpha>2,P2\<rangle> \<longleftrightarrow>
  (\<exists>p. supp (\<alpha>1, P1) - bn \<alpha>1 = supp (\<alpha>2, P2) - bn \<alpha>2 \<and> (supp (\<alpha>1, P1) - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> (\<alpha>1, P1) = (\<alpha>2, P2) \<and> p \<bullet> bn \<alpha>1 = bn \<alpha>2 \<and> supp p \<subseteq> bn \<alpha>1 \<union> p \<bullet> bn \<alpha>1)"
  (is "?l \<longleftrightarrow> ?r")
proof
  assume "?l"
  then obtain p where p: "supp (\<alpha>1, P1) - bn \<alpha>1 = supp (\<alpha>2, P2) - bn \<alpha>2 \<and> (supp (\<alpha>1, P1) - bn \<alpha>1) \<sharp>* p \<and> p \<bullet> (\<alpha>1, P1) = (\<alpha>2, P2) \<and> p \<bullet> bn \<alpha>1 = bn \<alpha>2"
    by (metis residual_eq_iff_perm)
  moreover obtain q where q_p: "\<forall>b\<in>bn \<alpha>1. q \<bullet> b = p \<bullet> b" and supp_q: "supp q \<subseteq> bn \<alpha>1 \<union> p \<bullet> bn \<alpha>1"
    by (metis set_renaming_perm2)
  have "supp q \<subseteq> supp p"
  proof
    fix a assume *: "a \<in> supp q" then show "a \<in> supp p"
    proof (cases "a \<in> bn \<alpha>1")
      case True then show ?thesis
        using "*" q_p by (metis mem_Collect_eq supp_perm)
    next
      case False then have "a \<in> p \<bullet> bn \<alpha>1"
        using "*" supp_q using UnE subsetCE by blast
      with False have "p \<bullet> a \<noteq> a"
        by (metis mem_permute_iff)
      then show ?thesis
        using fresh_def fresh_perm by blast
    qed
  qed
  with p have "(supp (\<alpha>1, P1) - bn \<alpha>1) \<sharp>* q"
    by (meson fresh_def fresh_star_def subset_iff)
  moreover with p and q_p have "\<And>a. a \<in> supp \<alpha>1 \<Longrightarrow> q \<bullet> a = p \<bullet> a" and "\<And>a. a \<in> supp P1 \<Longrightarrow> q \<bullet> a = p \<bullet> a"
    by (metis Diff_iff fresh_perm fresh_star_def UnCI supp_Pair)+
  then have "q \<bullet> \<alpha>1 = p \<bullet> \<alpha>1" and "q \<bullet> P1 = p \<bullet> P1"
    by (metis supp_perm_perm_eq)+
  ultimately show "?r"
    using supp_q by (metis Pair_eqvt bn_eqvt)
next
  assume "?r" then show "?l"
    by (meson residual_eq_iff_perm)
qed


subsection \<open>Strong induction\<close>

lemma residual_strong_induct:
  assumes "\<And>(act::'act::bn) (state::'state::fs) (c::'a::fs). bn act \<sharp>* c \<Longrightarrow> P c \<langle>act,state\<rangle>"
  shows "P c residual"
proof (rule residual.abs_induct, clarify)
  fix act :: 'act and state :: 'state
  obtain p where 1: "(p \<bullet> bn act) \<sharp>* c" and 2: "supp \<langle>act,state\<rangle> \<sharp>* p"
    proof (rule at_set_avoiding2[of "bn act" c "\<langle>act,state\<rangle>", THEN exE])
      show "finite (bn act)" by (fact bn_finite)
    next
      show "finite (supp c)" by (fact finite_supp)
    next
      show "finite (supp \<langle>act,state\<rangle>)" by (fact finite_supp_abs_residual_pair)
    next
      show "bn act \<sharp>* \<langle>act,state\<rangle>" by (fact bn_abs_residual_fresh)
    qed metis
  from 2 have "\<langle>p \<bullet> act, p \<bullet> state\<rangle> = \<langle>act,state\<rangle>"
    using supp_perm_eq by fastforce
  then show "P c \<langle>act,state\<rangle>"
    using assms 1 by (metis bn_eqvt)
qed


subsection \<open>Other lemmas\<close>

lemma residual_empty_bn_eq_iff:
  assumes "bn \<alpha>1 = {}"
  shows "\<langle>\<alpha>1,P1\<rangle> = \<langle>\<alpha>2,P2\<rangle> \<longleftrightarrow> \<alpha>1 = \<alpha>2 \<and> P1 = P2"
proof
  assume "\<langle>\<alpha>1,P1\<rangle> = \<langle>\<alpha>2,P2\<rangle>"
  with assms have "[{}]set. (\<alpha>1, P1) = [bn \<alpha>2]set. (\<alpha>2, P2)"
    by (simp add: residual.abs_eq_iff)
  then obtain p where "({}, (\<alpha>1, P1)) \<approx>set ((=)) supp p (bn \<alpha>2, (\<alpha>2, P2))"
    using Abs_eq_iff(1) by blast
  then show "\<alpha>1 = \<alpha>2 \<and> P1 = P2"
    unfolding alpha_set using supp_perm_eq by fastforce
next
  assume "\<alpha>1 = \<alpha>2 \<and> P1 = P2" then show "\<langle>\<alpha>1,P1\<rangle> = \<langle>\<alpha>2,P2\<rangle>"
    by simp
qed

\<comment> \<open>The following lemma is not about residuals, but we have no better place for it.\<close>
lemma set_bounded_supp:
  assumes "finite S" and "\<And>x. x\<in>X \<Longrightarrow> supp x \<subseteq> S"
  shows "supp X \<subseteq> S"
proof -
  have "S supports X"
    unfolding supports_def proof (clarify)
    fix a b
    assume a: "a \<notin> S" and b: "b \<notin> S"
    {
      fix x
      assume "x \<in> X"
      then have "(a \<rightleftharpoons> b) \<bullet> x = x"
        using a b \<open>\<And>x. x\<in>X \<Longrightarrow> supp x \<subseteq> S\<close> by (meson fresh_def subsetCE swap_fresh_fresh)
    }
    then show "(a \<rightleftharpoons> b) \<bullet> X = X"
      by auto (metis (full_types) eqvt_bound mem_permute_iff, metis mem_permute_iff)
  qed
  then show "supp X \<subseteq> S"
    using assms(1) by (fact supp_is_subset)
qed

end
