(*  Title:       AWN_Labels.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Labelling sequential processes"

theory AWN_Labels
imports AWN AWN_Cterms
begin

subsection "Labels "

text \<open>
  Labels serve two main purposes. They allow the substitution of @{term sterm}s in
  @{term invariant} proofs. They also allow the strengthening (control state dependent)
  of invariants.
\<close>

function (domintros) labels
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp \<Rightarrow> 'l set"
  where
    "labels \<Gamma> ({l}\<langle>fg\<rangle> p)                     = {l}"
  | "labels \<Gamma> ({l}\<lbrakk>fa\<rbrakk> p)                     = {l}"
  | "labels \<Gamma> (p1 \<oplus> p2)                      = labels \<Gamma> p1 \<union> labels \<Gamma> p2"
  | "labels \<Gamma> ({l}unicast(fip, fmsg).p \<triangleright> q)  = {l}"
  | "labels \<Gamma> ({l}broadcast(fmsg). p)         = {l}"
  | "labels \<Gamma> ({l}groupcast(fips, fmsg). p)   = {l}"
  | "labels \<Gamma> ({l}send(fmsg).p)               = {l}"
  | "labels \<Gamma> ({l}deliver(fdata).p)           = {l}"
  | "labels \<Gamma> ({l}receive(fmsg).p)            = {l}"
  | "labels \<Gamma> (call(pn))                      = labels \<Gamma> (\<Gamma> pn)"
  by pat_completeness auto

lemma labels_dom_basic [simp]:
  assumes "not_call p"
      and "not_choice p"
  shows "labels_dom (\<Gamma>, p)"
  proof (rule accpI)
    fix y
    assume "labels_rel y (\<Gamma>, p)"
    with assms show "labels_dom y"
      by (cases p) (auto simp: labels_rel.simps)
  qed

lemma labels_termination:
    fixes \<Gamma> p
  assumes "wellformed(\<Gamma>)"
    shows "labels_dom (\<Gamma>, p)"
  proof -
    have labels_rel': "labels_rel = (\<lambda>gq gp. (gq, gp) \<in> {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q})"
      by (rule ext)+ (auto simp: labels_rel.simps intro: microstep.intros elim: microstep.cases)
    from \<open>wellformed(\<Gamma>)\<close> have "\<forall>x. x \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      unfolding wellformed_def by (simp add: wf_acc_iff)
    hence "p \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}" ..
    hence "(\<Gamma>, p) \<in> Wellfounded.acc {((\<Gamma>, q), \<Gamma>', p). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      by (rule acc_induct) (auto intro: accI)
    thus "labels_dom (\<Gamma>, p)"
      unfolding labels_rel' by (subst accp_acc_eq)
  qed

declare labels.psimps[simp]

lemmas labels_pinduct = labels.pinduct [OF labels_termination]
   and labels_psimps[simp] = labels.psimps [OF labels_termination]

lemma labels_not_empty:
    fixes \<Gamma> p
  assumes "wellformed \<Gamma>"
    shows "labels \<Gamma> p \<noteq> {}"
   by (induct p rule: labels_pinduct [OF \<open>wellformed \<Gamma>\<close>]) simp_all

lemma has_label [dest]:
    fixes \<Gamma> p
  assumes "wellformed \<Gamma>"
    shows "\<exists>l. l \<in> labels \<Gamma> p"
  using labels_not_empty [OF assms] by auto

lemma singleton_labels [simp]:
  "\<And>\<Gamma> l l' f p.          l \<in> labels \<Gamma> ({l'}\<langle>f\<rangle> p)                       = (l = l')"
  "\<And>\<Gamma> l l' f p.          l \<in> labels \<Gamma> ({l'}\<lbrakk>f\<rbrakk> p)                      = (l = l')"
  "\<And>\<Gamma> l l' fip fmsg p q. l \<in> labels \<Gamma> ({l'}unicast(fip, fmsg).p \<triangleright> q)  = (l = l')"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}broadcast(fmsg). p)         = (l = l')"
  "\<And>\<Gamma> l l' fips fmsg p.  l \<in> labels \<Gamma> ({l'}groupcast(fips, fmsg). p)   = (l = l')"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}send(fmsg).p)               = (l = l')"
  "\<And>\<Gamma> l l' fdata p.      l \<in> labels \<Gamma> ({l'}deliver(fdata).p)           = (l = l')"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}receive(fmsg).p)            = (l = l')"
  by auto

lemma in_labels_singletons [dest!]:
  "\<And>\<Gamma> l l' f p.          l \<in> labels \<Gamma> ({l'}\<langle>f\<rangle> p)                       \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' f p.          l \<in> labels \<Gamma> ({l'}\<lbrakk>f\<rbrakk> p)                      \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fip fmsg p q. l \<in> labels \<Gamma> ({l'}unicast(fip, fmsg).p \<triangleright> q)  \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}broadcast(fmsg). p)         \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fips fmsg p.  l \<in> labels \<Gamma> ({l'}groupcast(fips, fmsg). p)   \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}send(fmsg).p)               \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fdata p.      l \<in> labels \<Gamma> ({l'}deliver(fdata).p)           \<Longrightarrow> l = l'"
  "\<And>\<Gamma> l l' fmsg p.       l \<in> labels \<Gamma> ({l'}receive(fmsg).p)            \<Longrightarrow> l = l'"
  by auto

definition
  simple_labels :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> bool"
where
  "simple_labels \<Gamma> \<equiv> \<forall>pn. \<forall>p\<in>subterms (\<Gamma> pn). (\<exists>!l. labels \<Gamma> p = {l})"

lemma simple_labelsI [intro]:
  assumes "\<And>pn p. p\<in>subterms (\<Gamma> pn) \<Longrightarrow> \<exists>!l. labels \<Gamma> p = {l}"
  shows "simple_labels \<Gamma>"
  using assms unfolding simple_labels_def by auto

text \<open>
  The @{term "simple_labels \<Gamma>"} property is necessary to transfer results shown over the
  @{term "cterms"} of a process specification @{term "\<Gamma>"} to the reachable actions of
  that process.

  Consider the process @{term "{l\<^sub>1}send(m1). p1 \<oplus> {l\<^sub>2}send(m2). p2"}. The iteration over @{term
  "cterms \<Gamma>"} will cover the two transitions
    @{term "(l\<^sub>1, send m1, p1)"} and
    @{term "(l\<^sub>2, send m2, p2)"},
  but reachability requires the four transitions
    @{term "(l\<^sub>1, send m1, p1)"},
    @{term "(l\<^sub>1, send m2, p2)"},
    @{term "(l\<^sub>2, send m1, p1)"}, and
    @{term "(l\<^sub>2, send m2, p2)"}.

  In a simply labelled process, the former is sufficient to show the latter, since
  @{term "l\<^sub>1 = l\<^sub>2"}.

  This requirement seems really only to be restrictive for processes where a @{term "call(pn)"}
  occurs as a direct subterm of a choice operator. Consider, for instance, @{term "({l\<^sub>1}\<lbrakk>e\<rbrakk> p) \<oplus>
  call(pn)"}. Here @{term "l\<^sub>1"} must equal the label of @{term "\<Gamma>(pn)"}, which can then not be
  distinguished from any other subterm that calls @{term "pn"} in any other process.

  This limitation stems from the fact that the "call points" of a process are effectively treated as
  the root of the called process. This is by design; we try to treat call sites as "syntactic
  pastings" of process terms, giving rise, conceptually, to an infinite tree structure. But this
  prejudices the alternative view that process calls are used as "join points" of "process threads",
  in complement to the "fork points" of the @{term "p1 \<oplus> p2"} operator.
\<close>

lemma simple_labels_in_sterms:
    fixes \<Gamma> l p
  assumes "simple_labels \<Gamma>"
      and "wellformed \<Gamma>"
      and "\<exists>pn. p\<in>subterms (\<Gamma> pn)"
      and "l\<in>labels \<Gamma> p"
    shows "\<forall>p'\<in>sterms \<Gamma> p. l\<in>labels \<Gamma> p'"
  using assms
  proof (induct p rule: labels_pinduct [OF \<open>wellformed \<Gamma>\<close>])
    fix \<Gamma> p1 p2
    assume sl: "simple_labels \<Gamma>"
       and wf: "wellformed \<Gamma>"
       and IH1: "\<lbrakk> simple_labels \<Gamma>; wellformed \<Gamma>;
                   \<exists>pn. p1 \<in> subterms (\<Gamma> pn); l \<in> labels \<Gamma> p1 \<rbrakk>
                 \<Longrightarrow> \<forall>p'\<in>sterms \<Gamma> p1. l \<in> labels \<Gamma> p'"
       and IH2: "\<lbrakk> simple_labels \<Gamma>; wellformed \<Gamma>;
                   \<exists>pn. p2 \<in> subterms (\<Gamma> pn); l \<in> labels \<Gamma> p2 \<rbrakk>
                 \<Longrightarrow> \<forall>p'\<in>sterms \<Gamma> p2. l \<in> labels \<Gamma> p'"
       and ein: "\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
       and l12: "l \<in> labels \<Gamma> (p1 \<oplus> p2)"
    from sl ein l12 have "labels \<Gamma> (p1 \<oplus> p2) = {l}"
      unfolding simple_labels_def by (metis empty_iff insert_iff)
    with wf have "labels \<Gamma> p1 \<union> labels \<Gamma> p2 = {l}" by simp
    moreover have "labels \<Gamma> p1 \<noteq> {}" and "labels \<Gamma> p2 \<noteq> {}"
      using wf by (metis labels_not_empty)+
    ultimately have "l \<in> labels \<Gamma> p1" and "l \<in> labels \<Gamma> p2"
      by (metis Un_iff empty_iff insert_iff set_eqI)+
    moreover from ein have "\<exists>pn. p1 \<in> subterms (\<Gamma> pn)"
                       and "\<exists>pn. p2 \<in> subterms (\<Gamma> pn)"
       by auto
    ultimately show "\<forall>p'\<in>sterms \<Gamma> (p1 \<oplus> p2). l\<in>labels \<Gamma> p'"
      using wf IH1 [OF sl wf] IH2 [OF sl wf] by auto
  qed auto

lemma labels_in_sterms:
    fixes \<Gamma> l p
  assumes "wellformed \<Gamma>"
      and "l\<in>labels \<Gamma> p"
    shows "\<exists>p'\<in>sterms \<Gamma> p. l\<in>labels \<Gamma> p'"
  using assms
  by (induct p rule: labels_pinduct [OF \<open>wellformed \<Gamma>\<close>]) (auto intro: Un_iff)

lemma labels_sterms_labels:
    fixes \<Gamma> p p' l
  assumes "wellformed \<Gamma>"
      and "p' \<in> sterms \<Gamma> p"
      and "l \<in> labels \<Gamma> p'"
    shows "l \<in> labels \<Gamma> p"
  using assms
  by (induct p rule: labels_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

primrec labelfrom :: "int \<Rightarrow> int \<Rightarrow> ('s, 'm, 'p, 'a) seqp \<Rightarrow> int \<times> ('s, 'm, 'p, int) seqp"
where
   "labelfrom n nn ({_}\<langle>f\<rangle> p)  =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}\<langle>f\<rangle> p'))"
 | "labelfrom n nn ({_}\<lbrakk>f\<rbrakk> p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}\<lbrakk>f\<rbrakk> p'))"
 | "labelfrom n nn (p \<oplus> q) =
      (let (nn', p') = labelfrom n nn p in
       let (nn'', q') = labelfrom n nn' q in
       (nn'', p' \<oplus> q'))"
 | "labelfrom n nn ({_}unicast(fip, fmsg). p \<triangleright> q) =
      (let (nn', p')  = labelfrom nn (nn + 1) p in
       let (nn'', q') = labelfrom nn' (nn' + 1) q in
       (nn'', {n}unicast(fip, fmsg). p' \<triangleright> q'))"
 | "labelfrom n nn ({_}broadcast(fmsg). p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}broadcast(fmsg). p'))"
 | "labelfrom n nn ({_}groupcast(fipset, fmsg). p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}groupcast(fipset, fmsg). p'))"
 | "labelfrom n nn ({_}send(fmsg). p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}send(fmsg). p'))"
 | "labelfrom n nn ({_}deliver(fdata). p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}deliver(fdata). p'))"
 | "labelfrom n nn ({_}receive(fmsg). p) =
      (let (nn', p') = labelfrom nn (nn + 1) p in
       (nn', {n}receive(fmsg). p'))"
 | "labelfrom n nn (call(fargs)) = (nn - 1, call(fargs))"

datatype 'pn label =
    LABEL 'pn int  ("_-:_" [1000, 1000] 999)

instantiation "label" :: (ord) ord
begin

fun less_eq_label :: "'a label \<Rightarrow> 'a label \<Rightarrow> bool"
where "(l1-:n1) \<le> (l2-:n2) = (l1 = l2 \<and> n1 \<le> n2)"

definition less_label: "(l1::'a label) < l2 \<longleftrightarrow> l1 \<le> l2 \<and> \<not> (l1 \<le> l2)"

instance ..
end

abbreviation labelled :: "'p \<Rightarrow> ('s, 'm, 'p, 'a) seqp \<Rightarrow> ('s, 'm, 'p, 'p label) seqp"
where "labelled pn p \<equiv> labelmap (\<lambda>l. LABEL pn l) (snd (labelfrom 0 1 p))"

end

