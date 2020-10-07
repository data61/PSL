(*  Title:       AWN_Cterms.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Control terms and well-definedness of sequential processes"

theory AWN_Cterms
imports AWN
begin

subsection "Microsteps "

text \<open>
  We distinguish microsteps from `external' transitions (observable or not). Here, they are
  a kind of `hypothetical computation', since, unlike \<open>\<tau>\<close>-transitions, they do not make
  choices but rather `compute' which choices are possible.
\<close>

inductive
  microstep :: "('s, 'm, 'p, 'l) seqp_env
                \<Rightarrow> ('s, 'm, 'p, 'l) seqp
                \<Rightarrow> ('s, 'm, 'p, 'l) seqp
                \<Rightarrow> bool"
for \<Gamma> :: "('s, 'm, 'p, 'l) seqp_env"
where
    microstep_choiceI1 [intro, simp]: "microstep \<Gamma> (p1 \<oplus> p2) p1"
  | microstep_choiceI2 [intro, simp]: "microstep \<Gamma> (p1 \<oplus> p2) p2"
  | microstep_callI [intro, simp]: "microstep \<Gamma> (call(pn)) (\<Gamma> pn)"

abbreviation microstep_rtcl
where "microstep_rtcl \<Gamma> p q \<equiv> (microstep \<Gamma>)\<^sup>*\<^sup>* p q"

abbreviation microstep_tcl
where "microstep_tcl \<Gamma> p q \<equiv> (microstep \<Gamma>)\<^sup>+\<^sup>+ p q"

syntax
  "_microstep"
     :: "[('s, 'm, 'p, 'l) seqp, ('s, 'm, 'p, 'l) seqp_env, ('s, 'm, 'p, 'l) seqp] \<Rightarrow> bool"
     ("(_) \<leadsto>\<^bsub>_\<^esub> (_)" [61, 0, 61] 50)
  "_microstep_rtcl"
     :: "[('s, 'm, 'p, 'l) seqp, ('s, 'm, 'p, 'l) seqp_env, ('s, 'm, 'p, 'l) seqp] \<Rightarrow> bool"
     ("(_) \<leadsto>\<^bsub>_\<^esub>\<^sup>* (_)" [61, 0, 61] 50)
  "_microstep_tcl"
     :: "[('s, 'm, 'p, 'l) seqp, ('s, 'm, 'p, 'l) seqp_env, ('s, 'm, 'p, 'l) seqp] \<Rightarrow> bool"
     ("(_) \<leadsto>\<^bsub>_\<^esub>\<^sup>+ (_)" [61, 0, 61] 50)

translations
  "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub> p2"  \<rightleftharpoons> "CONST microstep \<Gamma> p1 p2"
  "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p2" \<rightleftharpoons> "CONST microstep_rtcl \<Gamma> p1 p2"
  "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>+ p2" \<rightleftharpoons> "CONST microstep_tcl \<Gamma> p1 p2"

lemma microstep_choiceD [dest]:
  "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p \<Longrightarrow> p = p1 \<or> p = p2"
  by (ind_cases "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p") auto

lemma microstep_choiceE [elim]:
  "\<lbrakk> (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p;
     (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p1 \<Longrightarrow> P;
     (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p2 \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (blast)

lemma microstep_callD [dest]:
  "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> p \<Longrightarrow> p = \<Gamma> pn"
  by (ind_cases "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> p")

lemma microstep_callE [elim]:
  "\<lbrakk> (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> p;  p = \<Gamma>(pn) \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto

lemma no_microstep_guard: "\<not> (({l}\<langle>g\<rangle> p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}\<langle>g\<rangle> p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_assign: "\<not> ({l}\<lbrakk>f\<rbrakk> p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q"
  by (rule notI) (ind_cases "({l}\<lbrakk>f\<rbrakk> p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_unicast: "\<not> (({l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q) \<leadsto>\<^bsub>\<Gamma>\<^esub> r)"
  by (rule notI) (ind_cases "({l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q) \<leadsto>\<^bsub>\<Gamma>\<^esub> r")

lemma no_microstep_broadcast: "\<not> (({l}broadcast(s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}broadcast(s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_groupcast: "\<not> (({l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_send: "\<not> (({l}send(s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}send(s\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_deliver: "\<not> (({l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma no_microstep_receive: "\<not> (({l}receive(u\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  by (rule notI) (ind_cases "({l}receive(u\<^sub>m\<^sub>s\<^sub>g).p) \<leadsto>\<^bsub>\<Gamma>\<^esub> q")

lemma microstep_call_or_choice [dest]:
  assumes "p \<leadsto>\<^bsub>\<Gamma>\<^esub> q"
    shows "(\<exists>pn. p = call(pn)) \<or> (\<exists>p1 p2. p = p1 \<oplus> p2)"
  using assms by clarsimp (metis microstep.simps)

lemmas no_microstep [intro,simp] =
  no_microstep_guard
  no_microstep_assign
  no_microstep_unicast
  no_microstep_broadcast
  no_microstep_groupcast
  no_microstep_send
  no_microstep_deliver
  no_microstep_receive

subsection "Wellformed process specifications "

text \<open>
  A process specification \<open>\<Gamma>\<close> is wellformed if its @{term "microstep \<Gamma>"} relation is
  free of loops and infinite chains.

  For example, these specifications are not wellformed:
    @{term "\<Gamma>\<^sub>1(p1) = call(p1)"}

    @{term "\<Gamma>\<^sub>2(p1) = send(msg).call(p1) \<oplus> call(p1)"}

    @{term "\<Gamma>\<^sub>3(p1) = send(msg).call(p2)"}
    @{term "\<Gamma>\<^sub>3(p2) = call(p3)"}
    @{term "\<Gamma>\<^sub>3(p3) = call(p4)"}
    @{term "\<Gamma>\<^sub>3(p4) = call(p5)"}
    \ldots
\<close>

definition
  wellformed :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> bool"
where
  "wellformed \<Gamma> = wf {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"

lemma wellformed_defP: "wellformed \<Gamma> = wfP (\<lambda>q p. p \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  unfolding wellformed_def wfP_def by simp

text \<open>
  The induction rule for @{term "wellformed \<Gamma>"} is stronger than @{thm seqp.induct} because
  the case for @{term "call(pn)"} can be shown with the assumption on @{term "\<Gamma> pn"}.
\<close>

lemma wellformed_induct
  [consumes 1, case_names ASSIGN CHOICE CALL GUARD UCAST BCAST GCAST SEND DELIVER RECEIVE,
   induct set: wellformed]:
  assumes "wellformed \<Gamma>"
      and ASSIGN:  "\<And>l f p.          wellformed \<Gamma> \<Longrightarrow> P ({l}\<lbrakk>f\<rbrakk> p)"
      and GUARD:   "\<And>l f p.          wellformed \<Gamma> \<Longrightarrow> P ({l}\<langle>f\<rangle> p)"
      and UCAST:   "\<And>l fip fmsg p q. wellformed \<Gamma> \<Longrightarrow> P ({l}unicast(fip, fmsg). p \<triangleright> q)"
      and BCAST:   "\<And>l fmsg p.       wellformed \<Gamma> \<Longrightarrow> P ({l}broadcast(fmsg). p)"
      and GCAST:   "\<And>l fips fmsg p.  wellformed \<Gamma> \<Longrightarrow> P ({l}groupcast(fips, fmsg). p)"
      and SEND:    "\<And>l fmsg p.       wellformed \<Gamma> \<Longrightarrow> P ({l}send(fmsg). p)"
      and DELIVER: "\<And>l fdata p.      wellformed \<Gamma> \<Longrightarrow> P ({l}deliver(fdata). p)"
      and RECEIVE: "\<And>l fmsg p.       wellformed \<Gamma> \<Longrightarrow> P ({l}receive(fmsg). p)"
      and CHOICE:  "\<And>p1 p2.        \<lbrakk> wellformed \<Gamma>; P p1; P p2 \<rbrakk> \<Longrightarrow> P (p1 \<oplus> p2)"
      and CALL:    "\<And>pn.           \<lbrakk> wellformed \<Gamma>; P (\<Gamma> pn) \<rbrakk> \<Longrightarrow> P (call(pn))"
    shows "P a"
  using assms(1) unfolding wellformed_defP
  proof (rule wfP_induct_rule, case_tac x, simp_all)
    fix p1 p2
    assume "\<And>q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> q \<Longrightarrow> P q"
    then obtain "P p1" and "P p2" by (auto intro!: microstep.intros)
    thus "P (p1 \<oplus> p2)" by (rule CHOICE [OF \<open>wellformed \<Gamma>\<close>])
  next
    fix pn
    assume "\<And>q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> q \<Longrightarrow> P q"
    hence "P (\<Gamma> pn)" by (auto intro!: microstep.intros)
    thus "P (call(pn))" by (rule CALL [OF \<open>wellformed \<Gamma>\<close>])
  qed (auto intro: assms)

subsection "Start terms (sterms) "

text \<open>
  Formulate sets of local subterms from which an action is directly possible. Since the
  process specification @{term "\<Gamma>"} is not considered, only choice terms @{term "p1 \<oplus> p2"}
  are traversed, and not @{term "call(p)"} terms.
\<close>

fun stermsl :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p , 'l) seqp set"
where
    "stermsl (p1 \<oplus> p2) = stermsl p1 \<union> stermsl p2"
  | "stermsl p          = {p}"

lemma stermsl_nobigger: "q \<in> stermsl p \<Longrightarrow> size q \<le> size p"
  by (induct p) auto

lemma stermsl_no_choice[simp]: "p1 \<oplus> p2 \<notin> stermsl p"
  by (induct p) simp_all

lemma stermsl_choice_disj[simp]:
  "p \<in> stermsl (p1 \<oplus> p2) = (p \<in> stermsl p1 \<or> p \<in> stermsl p2)"
  by simp

lemma stermsl_in_branch[elim]:
  "\<lbrakk>p \<in> stermsl (p1 \<oplus> p2); p \<in> stermsl p1 \<Longrightarrow> P; p \<in> stermsl p2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma stermsl_commute:
  "stermsl (p1 \<oplus> p2) = stermsl (p2 \<oplus> p1)"
  by simp (rule Un_commute)

lemma stermsl_not_empty:
  "stermsl p \<noteq> {}"
  by (induct p) auto

lemma stermsl_idem [simp]:
  "(\<Union>q\<in>stermsl p. stermsl q) = stermsl p"
  by (induct p) simp_all

lemma stermsl_in_wfpf:
  assumes AA: "A \<subseteq> {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q} `` A"
      and *: "p \<in> A"
    shows "\<exists>r\<in>stermsl p. r \<in> A"
  using *
  proof (induction p)
    fix p1 p2
    assume IH1: "p1 \<in> A \<Longrightarrow> \<exists>r\<in>stermsl p1. r \<in> A"
       and IH2: "p2 \<in> A \<Longrightarrow> \<exists>r\<in>stermsl p2. r \<in> A"
       and *: "p1 \<oplus> p2 \<in> A"
    from * and AA have "p1 \<oplus> p2 \<in> {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q} `` A" by auto
    hence "p1 \<in> A \<or> p2 \<in> A" by auto
    hence "(\<exists>r\<in>stermsl p1. r \<in> A) \<or> (\<exists>r\<in>stermsl p2. r \<in> A)"
      proof
        assume "p1 \<in> A" hence "\<exists>r\<in>stermsl p1. r \<in> A" by (rule IH1) thus ?thesis ..
      next
        assume "p2 \<in> A" hence "\<exists>r\<in>stermsl p2. r \<in> A" by (rule IH2) thus ?thesis ..
      qed
      hence "\<exists>r\<in>stermsl p1 \<union> stermsl p2. r \<in> A" by blast
      thus "\<exists>r\<in>stermsl (p1 \<oplus> p2). r \<in> A" by simp
    next case UCAST from UCAST.prems show ?case by auto
  qed auto

lemma nocall_stermsl_max:
  assumes "r \<in> stermsl p"
      and "not_call r"
    shows "\<not> (r \<leadsto>\<^bsub>\<Gamma>\<^esub> q)"
  using assms
  by (induction p) auto

theorem wf_no_direct_calls[intro]:
    fixes \<Gamma> :: "('s, 'm, 'p, 'l) seqp_env"
  assumes no_calls: "\<And>pn. \<forall>pn'. call(pn') \<notin> stermsl(\<Gamma>(pn))"
    shows "wellformed \<Gamma>"
  unfolding wellformed_def wfP_def
  proof (rule wfI_pf)
    fix A
    assume ARA: "A \<subseteq> {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q} `` A"
    hence hasnext: "\<And>p. p \<in> A \<Longrightarrow> \<exists>q. p \<leadsto>\<^bsub>\<Gamma>\<^esub> q \<and> q \<in> A" by auto
    show "A = {}"
    proof (rule Set.equals0I)
      fix p assume "p \<in> A" thus "False"
      proof (induction p)
        fix l f p'
        assume *: "{l}\<langle>f\<rangle> p' \<in> A"
        from hasnext [OF *] have "\<exists>q. ({l}\<langle>f\<rangle> p') \<leadsto>\<^bsub>\<Gamma>\<^esub> q" by simp
        thus "False" by simp
      next
        fix p1 p2
        assume *: "p1 \<oplus> p2 \<in> A"
         and IH1: "p1 \<in> A \<Longrightarrow> False"
         and IH2: "p2 \<in> A \<Longrightarrow> False"
        have "\<exists>q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> q \<and> q \<in> A" by (rule hasnext [OF *])
        hence "p1 \<in> A \<or> p2 \<in> A" by auto
        thus "False" by (auto dest: IH1 IH2)
      next
        fix pn
        assume "call(pn) \<in> A"
        hence "\<exists>q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> q \<and> q \<in> A" by (rule hasnext)
        hence "\<Gamma>(pn) \<in> A" by auto

        with ARA [THEN stermsl_in_wfpf] obtain q where "q\<in>stermsl (\<Gamma> pn)" and "q \<in> A" by metis
        hence "not_call q" using no_calls [of pn]
          unfolding not_call_def by auto

        from hasnext [OF \<open>q \<in> A\<close>] obtain q' where "q \<leadsto>\<^bsub>\<Gamma>\<^esub> q'" by auto
        moreover from  \<open>q \<in> stermsl (\<Gamma> pn)\<close> \<open>not_call q\<close> have "\<not> (q \<leadsto>\<^bsub>\<Gamma>\<^esub> q')"
          by (rule nocall_stermsl_max)
        ultimately show "False" by simp
      qed (auto dest: hasnext)
    qed
  qed

subsection "Start terms"

text \<open>
  The start terms are those terms, relative to a wellformed process specification \<open>\<Gamma>\<close>,
  from which transitions can occur directly.
\<close>

function (domintros, sequential) sterms
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p, 'l) seqp set"
  where
    sterms_choice: "sterms \<Gamma> (p1 \<oplus> p2)  = sterms \<Gamma> p1 \<union> sterms \<Gamma> p2"
  | sterms_call:   "sterms \<Gamma> (call(pn))  = sterms \<Gamma> (\<Gamma> pn)"
  | sterms_other:  "sterms \<Gamma> p           = {p}"
  by pat_completeness auto

lemma sterms_dom_basic[simp]:
  assumes "not_call p"
      and "not_choice p"
    shows "sterms_dom (\<Gamma>, p)"
  proof (rule accpI)
    fix y
    assume "sterms_rel y (\<Gamma>, p)"
    with assms show "sterms_dom y"
      by (cases p) (auto simp: sterms_rel.simps)
  qed

lemma sterms_termination:
  assumes "wellformed \<Gamma>"
    shows "sterms_dom (\<Gamma>, p)"
  proof -
    have sterms_rel':
      "sterms_rel = (\<lambda>gq gp. (gq, gp) \<in> {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q})"
      by (rule ext)+ (auto simp: sterms_rel.simps elim: microstep.cases)

    from assms have "\<forall>x. x \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      unfolding wellformed_def by (simp add: wf_acc_iff)
    hence "p \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}" ..

    hence "(\<Gamma>, p) \<in> Wellfounded.acc {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      by (rule acc_induct) (auto intro: accI)

    thus "sterms_dom (\<Gamma>, p)" unfolding sterms_rel' accp_acc_eq .
  qed

declare sterms.psimps [simp]

lemmas sterms_psimps[simp] = sterms.psimps [OF sterms_termination]
   and sterms_pinduct = sterms.pinduct [OF sterms_termination]

lemma sterms_reflD [dest]:
  assumes "q \<in> sterms \<Gamma> p"
      and "not_choice p" "not_call p"
    shows "q = p"
  using assms by (cases p) auto

lemma sterms_choice_disj [simp]:
  assumes "wellformed \<Gamma>"
    shows "p \<in> sterms \<Gamma> (p1 \<oplus> p2) = (p \<in> sterms \<Gamma> p1 \<or> p \<in> sterms \<Gamma> p2)"
  using assms by (simp)

lemma sterms_no_choice [simp]:
  assumes "wellformed \<Gamma>"
    shows "p1 \<oplus> p2 \<notin> sterms \<Gamma> p"
  using assms by induction auto

lemma sterms_not_choice [simp]:
  assumes "wellformed \<Gamma>"
      and "q \<in> sterms \<Gamma> p"
    shows "not_choice q"
  using assms unfolding not_choice_def
  by (auto dest: sterms_no_choice)

lemma sterms_no_call [simp]:
  assumes "wellformed \<Gamma>"
    shows "call(pn) \<notin> sterms \<Gamma> p"
  using assms by induction auto

lemma sterms_not_call [simp]:
  assumes "wellformed \<Gamma>"
      and "q \<in> sterms \<Gamma> p"
    shows "not_call q"
  using assms unfolding not_call_def
  by (auto dest: sterms_no_call)

lemma sterms_in_branch:
  assumes "wellformed \<Gamma>"
      and "p \<in> sterms \<Gamma> (p1 \<oplus> p2)"
      and "p \<in> sterms \<Gamma> p1 \<Longrightarrow> P"
      and "p \<in> sterms \<Gamma> p2 \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma sterms_commute:
  assumes "wellformed \<Gamma>"
    shows "sterms \<Gamma> (p1 \<oplus> p2) = sterms \<Gamma> (p2 \<oplus> p1)"
  using assms by simp (rule Un_commute)

lemma sterms_not_empty:
  assumes "wellformed \<Gamma>"
    shows "sterms \<Gamma> p \<noteq> {}"
  using assms
  by (induct p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) simp_all

lemma sterms_sterms [simp]:
  assumes "wellformed \<Gamma>"
    shows "(\<Union>x\<in>sterms \<Gamma> p. sterms \<Gamma> x) = sterms \<Gamma> p"
  using assms by induction simp_all

lemma sterms_stermsl:
  assumes "ps \<in> sterms \<Gamma> p"
      and "wellformed \<Gamma>"
    shows "ps \<in> stermsl p \<or> (\<exists>pn. ps \<in> stermsl (\<Gamma> pn))"
  using assms by (induction p rule: sterms_pinduct [OF \<open>wellformed \<Gamma>\<close>]) auto

lemma stermsl_sterms [elim]:
  assumes "q \<in> stermsl p"
      and "not_call q"
      and "wellformed \<Gamma>"
    shows "q \<in> sterms \<Gamma> p"
  using assms by (induct p) auto

lemma sterms_stermsl_heads:
  assumes "ps \<in> sterms \<Gamma> (\<Gamma> pn)"
      and "wellformed \<Gamma>"
    shows "\<exists>pn. ps \<in> stermsl (\<Gamma> pn)"
  proof -
    from assms have "ps \<in> stermsl (\<Gamma> pn) \<or> (\<exists>pn'. ps \<in> stermsl (\<Gamma> pn'))"
      by (rule sterms_stermsl)
    thus ?thesis by auto
  qed

lemma sterms_subterms [dest]:
  assumes "wellformed \<Gamma>"
      and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      and "q \<in> sterms \<Gamma> p"
    shows "\<exists>pn. q \<in> subterms (\<Gamma> pn)"
  using assms by (induct p) auto

lemma no_microsteps_sterms_refl:
  assumes "wellformed \<Gamma>"
  shows "(\<not>(\<exists>q. p \<leadsto>\<^bsub>\<Gamma>\<^esub> q)) = (sterms \<Gamma> p = {p})"
  proof (cases p)
    fix p1 p2
    assume "p = p1 \<oplus> p2"
    from \<open>wellformed \<Gamma>\<close> have "p1 \<oplus> p2 \<notin> sterms \<Gamma> (p1 \<oplus> p2)" by simp
    hence "sterms \<Gamma> (p1 \<oplus> p2) \<noteq> {p1 \<oplus> p2}" by auto
    moreover have "\<exists>q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> q" by auto
    ultimately show ?thesis
      using \<open>p = p1 \<oplus> p2\<close> by simp
  next
    fix pn
    assume "p = call(pn)"
    from \<open>wellformed \<Gamma>\<close> have "call(pn) \<notin> sterms \<Gamma> (call(pn))" by simp
    hence "sterms \<Gamma> (call(pn)) \<noteq> {call(pn)}" by auto
    moreover have "\<exists>q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> q" by auto
    ultimately show ?thesis
      using \<open>p = call(pn)\<close> by simp
  qed simp_all

lemma sterms_maximal [elim]:
  assumes "wellformed \<Gamma>"
      and "q \<in> sterms \<Gamma> p"
    shows "sterms \<Gamma> q = {q}"
  using assms by (cases q) auto

lemma microstep_rtranscl_equal:
  assumes "not_call p"
      and "not_choice p"
      and "p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q"
    shows "q = p"
  using assms(3) proof (rule converse_rtranclpE)
    fix p'
    assume "p \<leadsto>\<^bsub>\<Gamma>\<^esub> p'"
    with assms(1-2) show "q = p"
      by (cases p) simp_all
  qed simp

lemma microstep_rtranscl_singleton [simp]:
  assumes "not_call p"
      and "not_choice p"
    shows "{q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} = {p}"
  proof (rule set_eqI)
    fix p'
    show "(p' \<in> {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}) = (p' \<in> {p})"
    proof
      assume "p' \<in> {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
      hence "(microstep \<Gamma>)\<^sup>*\<^sup>* p p'" and "sterms \<Gamma> p' = {p'}" by auto
      from this(1) have "p' = p"
      proof (rule converse_rtranclpE)
        fix q assume "p \<leadsto>\<^bsub>\<Gamma>\<^esub> q"
        with \<open>not_call p\<close> and \<open>not_choice p\<close> have False
          by (cases p) auto
        thus "p' = p" ..
      qed simp
      thus "p' \<in> {p}" by simp
    next
      assume "p' \<in> {p}"
      hence "p' = p" ..
      with \<open>not_call p\<close> and \<open>not_choice p\<close> show "p' \<in> {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
        by (cases p) simp_all
    qed
  qed

theorem sterms_maximal_microstep:
  assumes "wellformed \<Gamma>"
    shows "sterms \<Gamma> p = {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> \<not>(\<exists>q'. q \<leadsto>\<^bsub>\<Gamma>\<^esub> q')}"
  proof
    from \<open>wellformed \<Gamma>\<close> have "sterms \<Gamma> p \<subseteq> {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
    proof induction
     fix p1 p2
     assume IH1: "sterms \<Gamma> p1 \<subseteq> {q. p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
        and IH2: "sterms \<Gamma> p2 \<subseteq> {q. p2 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
     have "sterms \<Gamma> p1 \<subseteq> {q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
     proof
       fix p'
       assume "p' \<in> sterms \<Gamma> p1"
       with IH1 have "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'" by auto
       moreover have "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p1" ..
       ultimately have "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'"
         by - (rule converse_rtranclp_into_rtranclp)
       moreover from \<open>wellformed \<Gamma>\<close> and \<open>p' \<in> sterms \<Gamma> p1\<close> have "sterms \<Gamma> p' = {p'}" ..
       ultimately show "p' \<in> {q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
         by simp
     qed
     moreover have "sterms \<Gamma> p2 \<subseteq> {q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
     proof
       fix p'
       assume "p' \<in> sterms \<Gamma> p2"
       with IH2 have "p2 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'" and "sterms \<Gamma> p' = {p'}" by auto
       moreover have "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub> p2" ..
       ultimately have "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'"
         by - (rule converse_rtranclp_into_rtranclp)
       with \<open>sterms \<Gamma> p' = {p'}\<close> show "p' \<in> {q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
         by simp
     qed
     ultimately show "sterms \<Gamma> (p1 \<oplus> p2) \<subseteq> {q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
       using \<open>wellformed \<Gamma>\<close> by simp
    next
      fix pn
      assume IH: "sterms \<Gamma> (\<Gamma> pn) \<subseteq> {q. \<Gamma> pn \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
      show "sterms \<Gamma> (call(pn)) \<subseteq> {q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
      proof
        fix p'
        assume "p' \<in> sterms \<Gamma> (call(pn))"
        with \<open>wellformed \<Gamma>\<close> have "p' \<in> sterms \<Gamma> (\<Gamma> pn)" by simp
        with IH have "\<Gamma> pn \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'" and "sterms \<Gamma> p' = {p'}" by auto
        note this(1)
        moreover have "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> \<Gamma> pn" by simp
        ultimately have "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* p'"
          by - (rule converse_rtranclp_into_rtranclp)
        with \<open>sterms \<Gamma> p' = {p'}\<close> show "p' \<in> {q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}}"
          by simp
      qed
    qed simp_all
    with \<open>wellformed \<Gamma>\<close> show "sterms \<Gamma> p \<subseteq> {q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> \<not>(\<exists>q'. q \<leadsto>\<^bsub>\<Gamma>\<^esub> q')}"
      by (simp only: no_microsteps_sterms_refl)
  next
    from \<open>wellformed \<Gamma>\<close> have "{q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> p"
    proof (induction)
      fix p1 p2
      assume IH1: "{q. p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> p1"
         and IH2: "{q. p2 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> p2"
      show "{q. (p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> (p1 \<oplus> p2)"
      proof (rule, drule CollectD, erule conjE)
        fix q'
        assume "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
           and "sterms \<Gamma> q' = {q'}"
        with \<open>wellformed \<Gamma>\<close> have "(p1 \<oplus> p2) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>+ q'"          
          by (auto dest!: rtranclpD sterms_no_choice)
        hence "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q' \<or> p2 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
          by (auto dest: tranclpD)
        thus "q' \<in> sterms \<Gamma> (p1 \<oplus> p2)"
        proof
          assume "p1 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
          with IH1 and \<open>sterms \<Gamma> q' = {q'}\<close> have "q' \<in> sterms \<Gamma> p1" by auto
          with \<open>wellformed \<Gamma>\<close> show ?thesis by auto
        next
          assume "p2 \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
          with IH2 and \<open>sterms \<Gamma> q' = {q'}\<close> have "q' \<in> sterms \<Gamma> p2" by auto
          with \<open>wellformed \<Gamma>\<close> show ?thesis by auto
        qed
      qed
    next
      fix pn
      assume IH: "{q. \<Gamma> pn \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> (\<Gamma> pn)"
      show   "{q. (call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> sterms \<Gamma> q = {q}} \<subseteq> sterms \<Gamma> (call(pn))"
      proof (rule, drule CollectD, erule conjE)
        fix q'
        assume "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
           and "sterms \<Gamma> q' = {q'}"
        with \<open>wellformed \<Gamma>\<close> have "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>+ q'"
          by (auto dest!: rtranclpD sterms_no_call)
        moreover have "(call(pn)) \<leadsto>\<^bsub>\<Gamma>\<^esub> \<Gamma> pn" ..
        ultimately have "\<Gamma> pn \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q'"
          by (auto dest!: tranclpD)
        with \<open>sterms \<Gamma> q' = {q'}\<close> and IH have "q' \<in> sterms \<Gamma> (\<Gamma> pn)" by auto
        with \<open>wellformed \<Gamma>\<close> show "q' \<in> sterms \<Gamma> (call(pn))" by simp
      qed
    qed simp_all
    with \<open>wellformed \<Gamma>\<close> show "{q. p \<leadsto>\<^bsub>\<Gamma>\<^esub>\<^sup>* q \<and> \<not>(\<exists>q'. q \<leadsto>\<^bsub>\<Gamma>\<^esub> q')} \<subseteq> sterms \<Gamma> p"
    by (simp only: no_microsteps_sterms_refl)
  qed

subsection "Derivative terms "

text \<open>
  The derivatives of a term are those @{term sterm}s potentially reachable by taking a
  transition, relative to a wellformed process specification \<open>\<Gamma>\<close>. These terms
  overapproximate the reachable sterms, since the truth of guards is not considered.
\<close>

function (domintros) dterms
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p, 'l) seqp set"
  where
    "dterms \<Gamma> ({l}\<langle>g\<rangle> p)                     = sterms \<Gamma> p"
  | "dterms \<Gamma> ({l}\<lbrakk>u\<rbrakk> p)                     = sterms \<Gamma> p"
  | "dterms \<Gamma> (p1 \<oplus> p2)                     = dterms \<Gamma> p1 \<union> dterms \<Gamma> p2"
  | "dterms \<Gamma> ({l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q)  = sterms \<Gamma> p \<union> sterms \<Gamma> q"
  | "dterms \<Gamma> ({l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p)        = sterms \<Gamma> p"
  | "dterms \<Gamma> ({l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p)  = sterms \<Gamma> p"
  | "dterms \<Gamma> ({l}send(s\<^sub>m\<^sub>s\<^sub>g).p)              = sterms \<Gamma> p"
  | "dterms \<Gamma> ({l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a).p)          = sterms \<Gamma> p"
  | "dterms \<Gamma> ({l}receive(u\<^sub>m\<^sub>s\<^sub>g).p)           = sterms \<Gamma> p"
  | "dterms \<Gamma> (call(pn))                     = dterms \<Gamma> (\<Gamma> pn)"
  by pat_completeness auto

lemma dterms_dom_basic [simp]:
  assumes "not_call p"
      and "not_choice p"
    shows "dterms_dom (\<Gamma>, p)"
  proof (rule accpI)
    fix y
    assume "dterms_rel y (\<Gamma>, p)"
    with assms show "dterms_dom y"
      by (cases p) (auto simp: dterms_rel.simps)
  qed

lemma dterms_termination:
  assumes "wellformed \<Gamma>"
    shows "dterms_dom (\<Gamma>, p)"
  proof -
    have dterms_rel': "dterms_rel = (\<lambda>gq gp. (gq, gp) \<in> {((\<Gamma>, q), (\<Gamma>', p)). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q})"
      by (rule ext)+ (auto simp: dterms_rel.simps elim: microstep.cases)
    from \<open>wellformed(\<Gamma>)\<close> have "\<forall>x. x \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      unfolding wellformed_def by (simp add: wf_acc_iff)
    hence "p \<in> Wellfounded.acc {(q, p). p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}" ..
    hence "(\<Gamma>, p) \<in> Wellfounded.acc {((\<Gamma>, q), \<Gamma>', p). \<Gamma> = \<Gamma>' \<and> p \<leadsto>\<^bsub>\<Gamma>\<^esub> q}"
      by (rule acc_induct) (auto intro: accI)
    thus "dterms_dom (\<Gamma>, p)"
      unfolding dterms_rel' by (subst accp_acc_eq)
  qed

lemmas dterms_psimps [simp] = dterms.psimps [OF dterms_termination]
   and dterms_pinduct = dterms.pinduct [OF dterms_termination]

lemma sterms_after_dterms [simp]:
  assumes "wellformed \<Gamma>"
  shows "(\<Union>x\<in>dterms \<Gamma> p. sterms \<Gamma> x) = dterms \<Gamma> p"
  using assms by (induction p) simp_all

lemma sterms_before_dterms [simp]:
  assumes "wellformed \<Gamma>"
  shows "(\<Union>x\<in>sterms \<Gamma> p. dterms \<Gamma> x) = dterms \<Gamma> p"
  using assms by (induction p) simp_all

lemma dterms_choice_disj [simp]:
  assumes "wellformed \<Gamma>"
    shows "p \<in> dterms \<Gamma> (p1 \<oplus> p2) = (p \<in> dterms \<Gamma> p1 \<or> p \<in> dterms \<Gamma> p2)"
  using assms by (simp)

lemma dterms_in_branch:
  assumes "wellformed \<Gamma>"
      and "p \<in> dterms \<Gamma> (p1 \<oplus> p2)"
      and "p \<in> dterms \<Gamma> p1 \<Longrightarrow> P"
      and "p \<in> dterms \<Gamma> p2 \<Longrightarrow> P"
  shows "P"
  using assms by auto

lemma dterms_no_choice:
  assumes "wellformed \<Gamma>"
    shows "p1 \<oplus> p2 \<notin> dterms \<Gamma> p"
  using assms by induction simp_all

lemma dterms_not_choice [simp]:
  assumes "wellformed \<Gamma>"
      and "q \<in> dterms \<Gamma> p"
    shows "not_choice q"
  using assms unfolding not_choice_def
  by (auto dest: dterms_no_choice)

lemma dterms_no_call:
  assumes "wellformed \<Gamma>"
    shows "call(pn) \<notin> dterms \<Gamma> p"
  using assms by induction simp_all

lemma dterms_not_call [simp]:
  assumes "wellformed \<Gamma>"
      and "q \<in> dterms \<Gamma> p"
    shows "not_call q"
  using assms unfolding not_call_def
  by (auto dest: dterms_no_call)

lemma dterms_subterms:
  assumes wf: "wellformed \<Gamma>"
      and "\<exists>pn. p \<in> subterms (\<Gamma> pn)"
      and "q \<in> dterms \<Gamma> p"
    shows "\<exists>pn. q \<in> subterms (\<Gamma> pn)"
  using assms
  proof (induct p)
       fix p1 p2
    assume IH1: "\<exists>pn. p1 \<in> subterms (\<Gamma> pn) \<Longrightarrow> q \<in> dterms \<Gamma> p1 \<Longrightarrow> \<exists>pn. q \<in> subterms (\<Gamma> pn)"
       and IH2: "\<exists>pn. p2 \<in> subterms (\<Gamma> pn) \<Longrightarrow> q \<in> dterms \<Gamma> p2 \<Longrightarrow> \<exists>pn. q \<in> subterms (\<Gamma> pn)"
       and *: "\<exists>pn. p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
       and "q \<in> dterms \<Gamma> (p1 \<oplus> p2)"
    from * obtain pn where "p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
      by auto
    hence "p1 \<in> subterms (\<Gamma> pn)" and "p2 \<in> subterms (\<Gamma> pn)"
      by auto
    from \<open>q \<in> dterms \<Gamma> (p1 \<oplus> p2)\<close> wf have "q \<in> dterms \<Gamma> p1 \<or> q \<in> dterms \<Gamma> p2"
      by auto
    thus "\<exists>pn. q \<in> subterms (\<Gamma> pn)"
      proof
        assume "q \<in> dterms \<Gamma> p1"
        with \<open>p1 \<in> subterms (\<Gamma> pn)\<close> show ?thesis
          by (auto intro: IH1)
      next
        assume "q \<in> dterms \<Gamma> p2"
        with \<open>p2 \<in> subterms (\<Gamma> pn)\<close> show ?thesis
          by (auto intro: IH2)
      qed
  qed auto

text \<open>
  Note that the converse of @{thm dterms_subterms} is not true because @{term dterm}s are an
  over-approximation; i.e., we cannot show, in general, that guards return a non-empty set
  of post-states.
\<close>

subsection "Control terms "

text \<open>
  The control terms of a process specification @{term \<Gamma>} are those subterms from which
  transitions are directly possible. We can omit @{term "call(pn)"} terms, since
  the root terms of all processes are considered, and also @{term "p1 \<oplus> p2"} terms
  since they effectively combine the transitions of the subterms @{term p1} and
  @{term p2}.

  It will be shown that only the control terms, rather than all subterms, need be
  considered in invariant proofs.
\<close>

inductive_set
  cterms :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s, 'm, 'p, 'l) seqp set"
  for \<Gamma> :: "('s, 'm, 'p, 'l) seqp_env"
where
    ctermsSI[intro]: "p \<in> sterms \<Gamma> (\<Gamma> pn) \<Longrightarrow> p \<in> cterms \<Gamma>"
  | ctermsDI[intro]: "\<lbrakk> pp \<in> cterms \<Gamma>; p \<in> dterms \<Gamma> pp \<rbrakk> \<Longrightarrow> p \<in> cterms \<Gamma>"

lemma cterms_not_choice [simp]:
  assumes "wellformed \<Gamma>"
      and "p \<in> cterms \<Gamma>"
    shows "not_choice p"
  using assms
  proof (cases p)
    case CHOICE from \<open>p \<in> cterms \<Gamma>\<close> show ?thesis
      using \<open>wellformed \<Gamma>\<close> by cases simp_all
  qed simp_all

lemma cterms_no_choice [simp]:
  assumes "wellformed \<Gamma>"
    shows "p1 \<oplus> p2 \<notin> cterms \<Gamma>"
  using assms by (auto dest: cterms_not_choice)

lemma cterms_not_call [simp]:
  assumes "wellformed \<Gamma>"
      and "p \<in> cterms \<Gamma>"
    shows "not_call p"
  using assms
  proof (cases p)
    case CALL from \<open>p \<in> cterms \<Gamma>\<close> show ?thesis
      using \<open>wellformed \<Gamma>\<close> by cases simp_all
  qed simp_all

lemma cterms_no_call [simp]:
  assumes "wellformed \<Gamma>"
    shows "call(pn) \<notin> cterms \<Gamma>"
  using assms by (auto dest: cterms_not_call)

lemma sterms_cterms [elim]:
  assumes "p \<in> cterms \<Gamma>"
      and "q \<in> sterms \<Gamma> p"
      and "wellformed \<Gamma>"
    shows "q \<in> cterms \<Gamma>"
  using assms by - (cases p, auto)

lemma dterms_cterms [elim]:
  assumes "p \<in> cterms \<Gamma>"
      and "q \<in> dterms \<Gamma> p"
      and "wellformed \<Gamma>"
    shows "q \<in> cterms \<Gamma>"
  using assms by (cases p) auto

lemma derivs_in_cterms [simp]:
  "\<And>l f p. {l}\<langle>f\<rangle> p \<in> cterms \<Gamma>                            \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l f p. {l}\<lbrakk>f\<rbrakk> p \<in> cterms \<Gamma>                           \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l fip fmsg q p. {l}unicast(fip, fmsg). p \<triangleright> q \<in> cterms \<Gamma>
                            \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma> \<and> sterms \<Gamma> q \<subseteq> cterms \<Gamma>"
  "\<And>l fmsg p.      {l}broadcast(fmsg).p \<in> cterms \<Gamma>       \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l fips fmsg p. {l}groupcast(fips, fmsg).p \<in> cterms \<Gamma> \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l fmsg p.      {l}send(fmsg).p \<in> cterms \<Gamma>            \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l fdata p.     {l}deliver(fdata).p \<in> cterms \<Gamma>        \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  "\<And>l fmsg p.      {l}receive(fmsg).p \<in> cterms \<Gamma>         \<Longrightarrow> sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  by (auto simp: dterms.psimps)

subsection "Local control terms"

text \<open>
  We introduce a `local' version of @{term cterms} that does not step through calls and,
  thus, that is defined independently of a process specification @{term \<Gamma>}.
  This allows an alternative, terminating characterisation of cterms as a set of
  subterms. Including @{term "call(pn)"}s in the set makes for a simpler relation with
  @{term "stermsl"}, even if they must be filtered out for the desired characterisation.
\<close>

function
  ctermsl :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p , 'l) seqp set"
where
    "ctermsl ({l}\<langle>g\<rangle> p)                     = insert ({l}\<langle>g\<rangle> p)  (ctermsl p)"
  | "ctermsl ({l}\<lbrakk>u\<rbrakk> p)                     = insert ({l}\<lbrakk>u\<rbrakk> p)  (ctermsl p)"
  | "ctermsl ({l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q) = insert ({l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q)
                                                                      (ctermsl p \<union> ctermsl q)"
  | "ctermsl ({l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p)       = insert ({l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p)       (ctermsl p)"
  | "ctermsl ({l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p)  = insert ({l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p) (ctermsl p)"
  | "ctermsl ({l}send(s\<^sub>m\<^sub>s\<^sub>g). p)            = insert ({l}send(s\<^sub>m\<^sub>s\<^sub>g). p)            (ctermsl p)"
  | "ctermsl ({l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p)        = insert ({l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p)        (ctermsl p)"
  | "ctermsl ({l}receive(u\<^sub>m\<^sub>s\<^sub>g). p)         = insert ({l}receive(u\<^sub>m\<^sub>s\<^sub>g). p)         (ctermsl p)"
  | "ctermsl (p1 \<oplus> p2)                    = ctermsl p1 \<union> ctermsl p2"
  | "ctermsl (call(pn))                   = {call(pn)}"
  by pat_completeness auto
  termination by (relation "measure(size)") (auto dest: stermsl_nobigger)

lemmas ctermsl_induct =
  ctermsl.induct [case_names GUARD ASSIGN UCAST BCAST GCAST
                             SEND DELIVER RECEIVE CHOICE CALL]

lemma ctermsl_refl [intro]: "not_choice p \<Longrightarrow> p \<in> ctermsl p"
  by (cases p) auto

lemma ctermsl_subterms:
  "ctermsl p = {q. q \<in> subterms p \<and> not_choice q }" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs" by (induct p, auto) next
    show "?rhs \<subseteq> ?lhs" by (induct p, auto)
  qed

lemma ctermsl_trans [elim]:
  assumes "q \<in> ctermsl p"
      and "r \<in> ctermsl q"
    shows "r \<in> ctermsl p"
  using assms
  proof (induction p rule: ctermsl_induct)
    case (CHOICE p1 p2)
      have "(q \<in> ctermsl p1) \<or> (q \<in> ctermsl p2)"
        using CHOICE.prems(1) by simp
      hence "r \<in> ctermsl p1 \<or> r \<in> ctermsl p2"
      proof (rule disj_forward)
        assume "q \<in> ctermsl p1"
        thus "r \<in> ctermsl p1" using \<open>r \<in> ctermsl q\<close> by (rule CHOICE.IH)
      next
        assume "q \<in> ctermsl p2"
        thus "r \<in> ctermsl p2" using \<open>r \<in> ctermsl q\<close> by (rule CHOICE.IH)
      qed
      thus "r \<in> ctermsl (p1 \<oplus> p2)" by simp
    qed auto

lemma ctermsl_ex_trans [elim]:
  assumes "\<exists>q \<in> ctermsl p. r \<in> ctermsl q"
    shows "r \<in> ctermsl p"
  using assms by auto

lemma call_ctermsl_empty [elim]:
  "\<lbrakk> p \<in> ctermsl p'; not_call p \<rbrakk> \<Longrightarrow> not_call p'"
  unfolding not_call_def by (cases p) auto

lemma stermsl_ctermsl_choice1 [simp]:
  assumes "q \<in> stermsl p1"
    shows "q \<in> ctermsl (p1 \<oplus> p2)"
  using assms by (induction p1) auto

lemma stermsl_ctermsl_choice2 [simp]:
  assumes "q \<in> stermsl p2"
    shows "q \<in> ctermsl (p1 \<oplus> p2)"
  using assms by (induction p2) auto

lemma stermsl_ctermsl [elim]:
  assumes "q \<in> stermsl p"
    shows "q \<in> ctermsl p"
  using assms
  proof (cases p)
    case (CHOICE p1 p2)
    hence "q \<in> stermsl (p1 \<oplus> p2)" using assms by simp
    hence "q \<in> stermsl p1 \<or> q \<in> stermsl p2" by simp
    hence "q \<in> ctermsl (p1 \<oplus> p2)" by (rule) (simp_all del: ctermsl.simps)
    thus  "q \<in> ctermsl p" using CHOICE by simp
  qed simp_all

lemma stermsl_after_ctermsl [simp]:
  "(\<Union>x\<in>ctermsl p. stermsl x) = ctermsl p"
  by (induct p) auto

lemma stermsl_before_ctermsl [simp]:
  "(\<Union>x\<in>stermsl p. ctermsl x) = ctermsl p"
  by (induct p) simp_all

lemma ctermsl_no_choice: "p1 \<oplus> p2 \<notin> ctermsl p"
  by (induct p) simp_all

lemma ctermsl_ex_stermsl: "q \<in> ctermsl p \<Longrightarrow> \<exists>ps\<in>stermsl p. q \<in> ctermsl ps"
  by (induct p) auto

lemma dterms_ctermsl [intro]:
  assumes "q \<in> dterms \<Gamma> p"
      and "wellformed \<Gamma>"
    shows "q \<in> ctermsl p \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
  using assms(1-2)
  proof (induction p rule: dterms_pinduct [OF \<open>wellformed \<Gamma>\<close>])
    fix \<Gamma> l fg p
    assume "q \<in> dterms \<Gamma> ({l}\<langle>fg\<rangle> p)"
       and "wellformed \<Gamma>"
    hence "q \<in> sterms \<Gamma> p" by simp
    hence "q \<in> stermsl p \<or> (\<exists>pn. q \<in> stermsl (\<Gamma> pn))"
      using \<open>wellformed \<Gamma>\<close>  by (rule sterms_stermsl)
    thus "q \<in> ctermsl ({l}\<langle>fg\<rangle> p) \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
    proof
      assume "q \<in> stermsl p"
      hence "q \<in> ctermsl p" by (rule stermsl_ctermsl)
      hence "q \<in> ctermsl ({l}\<langle>fg\<rangle> p)" by simp
      thus ?thesis ..
    next
      assume "\<exists>pn. q \<in> stermsl (\<Gamma> pn)"
      then obtain pn where "q \<in> stermsl (\<Gamma> pn)" by auto
      hence "q \<in> ctermsl (\<Gamma> pn)" by (rule stermsl_ctermsl)
      hence "\<exists>pn. q \<in> ctermsl (\<Gamma> pn)" ..
      thus ?thesis ..
    qed
  next
    fix \<Gamma> p1 p2
    assume "q \<in> dterms \<Gamma> (p1 \<oplus> p2)"
       and IH1: "\<lbrakk> q \<in> dterms \<Gamma> p1; wellformed \<Gamma> \<rbrakk> \<Longrightarrow> q \<in> ctermsl p1 \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
       and IH2: "\<lbrakk> q \<in> dterms \<Gamma> p2; wellformed \<Gamma> \<rbrakk> \<Longrightarrow> q \<in> ctermsl p2 \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
       and "wellformed \<Gamma>"
    thus "q \<in> ctermsl (p1 \<oplus> p2) \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
      by auto
  next
    fix \<Gamma> pn
    assume "q \<in> dterms \<Gamma> (call(pn))"
       and "wellformed \<Gamma>"
       and "\<lbrakk> q \<in> dterms \<Gamma> (\<Gamma> pn); wellformed \<Gamma> \<rbrakk> \<Longrightarrow> q \<in> ctermsl (\<Gamma> pn) \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
    thus "q \<in> ctermsl (call(pn)) \<or> (\<exists>pn. q \<in> ctermsl (\<Gamma> pn))"
      by auto
  qed (simp_all, (metis sterms_stermsl stermsl_ctermsl)+)

lemma ctermsl_cterms [elim]:
  assumes "q \<in> ctermsl p"
      and "not_call q"
      and "sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
      and "wellformed \<Gamma>"
    shows "q \<in> cterms \<Gamma>"
  using assms by (induct p rule: ctermsl.induct) auto

subsection "Local deriviative terms"

text \<open>
  We define local @{term "dterm"}s for use in the theorem that relates @{term "cterms"}
  and sets of @{term "ctermsl"}.
\<close>

function dtermsl
  :: "('s, 'm, 'p, 'l) seqp \<Rightarrow> ('s, 'm, 'p, 'l) seqp set"
  where
    "dtermsl ({l}\<langle>fg\<rangle> p)                     = stermsl p"
  | "dtermsl ({l}\<lbrakk>fa\<rbrakk> p)                     = stermsl p"
  | "dtermsl (p1 \<oplus> p2)                      = dtermsl p1 \<union> dtermsl p2"
  | "dtermsl ({l}unicast(fip, fmsg).p \<triangleright> q)  = stermsl p \<union> stermsl q"
  | "dtermsl ({l}broadcast(fmsg). p)         = stermsl p"
  | "dtermsl ({l}groupcast(fips, fmsg). p)   = stermsl p"
  | "dtermsl ({l}send(fmsg).p)               = stermsl p"
  | "dtermsl ({l}deliver(fdata).p)           = stermsl p"
  | "dtermsl ({l}receive(fmsg).p)            = stermsl p"
  | "dtermsl (call(pn))                      = {}"
  by pat_completeness auto
  termination by (relation "measure(size)") (auto dest: stermsl_nobigger)

lemma stermsl_after_dtermsl [simp]:
  shows "(\<Union>x\<in>dtermsl p. stermsl x) = dtermsl p"
  by (induct p) simp_all

lemma stermsl_before_dtermsl [simp]:
  "(\<Union>x\<in>stermsl p. dtermsl x) = dtermsl p"
  by (induct p) simp_all

lemma dtermsl_no_choice [simp]: "p1 \<oplus> p2 \<notin> dtermsl p"
  by (induct p) simp_all

lemma dtermsl_choice_disj [simp]:
  "p \<in> dtermsl (p1 \<oplus> p2) = (p \<in> dtermsl p1 \<or> p \<in> dtermsl p2)"
  by simp

lemma dtermsl_in_branch [elim]:
  "\<lbrakk>p \<in> dtermsl (p1 \<oplus> p2); p \<in> dtermsl p1 \<Longrightarrow> P; p \<in> dtermsl p2 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma ctermsl_dtermsl [elim]:
  assumes "q \<in> dtermsl p"
    shows "q \<in> ctermsl p"
  using assms by (induct p) (simp_all, (metis stermsl_ctermsl)+)

lemma dtermsl_dterms [elim]:
  assumes "q \<in> dtermsl p"
      and "not_call q"
      and "wellformed \<Gamma>"
    shows "q \<in> dterms \<Gamma> p"
  using assms
  using assms by (induct p) (simp_all, (metis stermsl_sterms)+)

lemma ctermsl_stermsl_or_dtermsl:
  assumes "q \<in> ctermsl p"
    shows "q \<in> stermsl p \<or> (\<exists>p'\<in>dtermsl p. q \<in> ctermsl p')"
  using assms by (induct p) (auto dest: ctermsl_ex_stermsl)

lemma dtermsl_add_stermsl_beforeD:
  assumes "q \<in> dtermsl p"
    shows "\<exists>ps\<in>stermsl p. q \<in> dtermsl ps"
  proof -
    from assms have "q \<in> (\<Union>x\<in>stermsl p. dtermsl x)" by auto
    thus ?thesis
      by (rule UN_E) auto
  qed

lemma call_dtermsl_empty [elim]:
 "q \<in> dtermsl p \<Longrightarrow> not_call p"
  by (cases p) simp_all

subsection "More properties of control terms"

text \<open>
  We now show an alternative definition of @{term "cterms"} based on sets of local control
  terms. While the original definition has convenient induction and simplification rules,
  useful for proving properties like cterms\_includes\_sterms\_of\_seq\_reachable, this
  definition makes it easier to systematically generate the set of control terms of a
  process specification.
\<close>

theorem cterms_def':
  assumes wfg: "wellformed \<Gamma>"
    shows "cterms \<Gamma> = { p |p pn. p \<in> ctermsl (\<Gamma> pn) \<and> not_call p }"
          (is "_ = ?ctermsl_set")
  proof (rule iffI [THEN set_eqI])
    fix p
    assume "p \<in> cterms \<Gamma>"
    thus "p \<in> ?ctermsl_set"
    proof (induction p)
      fix p pn
      assume "p \<in> sterms \<Gamma> (\<Gamma> pn)"
      then obtain pn' where "p \<in> stermsl (\<Gamma> pn')" using wfg
        by (blast dest: sterms_stermsl_heads)
      hence "p \<in> ctermsl (\<Gamma> pn')" ..
      moreover from \<open>p \<in> sterms \<Gamma> (\<Gamma> pn)\<close> wfg have "not_call p" by simp
      ultimately show "p \<in> ?ctermsl_set" by auto
    next
      fix pp p
      assume "pp \<in> cterms \<Gamma>"
         and IH: "pp \<in> ?ctermsl_set"
         and *: "p \<in> dterms \<Gamma> pp"
      from * have "p \<in> ctermsl pp \<or> (\<exists>pn. p \<in> ctermsl (\<Gamma> pn))"
        using wfg by (rule dterms_ctermsl)
      hence "\<exists>pn. p \<in> ctermsl (\<Gamma> pn)"
        proof
          assume "p \<in> ctermsl pp"
          from \<open>pp \<in> cterms \<Gamma>\<close> and IH obtain pn' where "pp \<in> ctermsl (\<Gamma> pn')"
            by auto
          with \<open>p \<in> ctermsl pp\<close> have "p \<in> ctermsl (\<Gamma> pn')" by auto
          thus "\<exists>pn. p \<in> ctermsl (\<Gamma> pn)" ..
        qed -
      moreover from \<open>p \<in> dterms \<Gamma> pp\<close> wfg have "not_call p" by simp
      ultimately show "p \<in> ?ctermsl_set" by auto
    qed
  next
    fix p
    assume "p \<in> ?ctermsl_set"
    then obtain pn where *: "p \<in> ctermsl (\<Gamma> pn)" and "not_call p" by auto
    from * have "p \<in> stermsl (\<Gamma> pn) \<or> (\<exists>p'\<in>dtermsl (\<Gamma> pn). p \<in> ctermsl p')"
      by (rule ctermsl_stermsl_or_dtermsl)
    thus "p \<in> cterms \<Gamma>"
    proof
      assume "p \<in> stermsl (\<Gamma> pn)"
      hence "p \<in> sterms \<Gamma> (\<Gamma> pn)" using \<open>not_call p\<close> wfg ..
      thus "p \<in> cterms \<Gamma>" ..
    next
      assume "\<exists>p'\<in>dtermsl (\<Gamma> pn). p \<in> ctermsl p'"
      then obtain p' where p'1: "p' \<in> dtermsl (\<Gamma> pn)"
                       and p'2: "p \<in> ctermsl p'" ..
      from p'2 and \<open>not_call p\<close> have "not_call p'" ..
      from p'1 obtain ps where ps1: "ps \<in> stermsl (\<Gamma> pn)"
                           and ps2: "p' \<in> dtermsl ps"
        by (blast dest: dtermsl_add_stermsl_beforeD)
      from ps2 have "not_call ps" ..
      with ps1 have "ps \<in> cterms \<Gamma>" using wfg by auto
      with \<open>p' \<in> dtermsl ps\<close> and \<open>not_call p'\<close> have "p' \<in> cterms \<Gamma>" using wfg by auto
      hence "sterms \<Gamma> p' \<subseteq> cterms \<Gamma>" using wfg by auto
      with \<open>p \<in> ctermsl p'\<close> \<open>not_call p\<close> show "p \<in> cterms \<Gamma>" using wfg ..
    qed
  qed

lemma ctermsE [elim]:
  assumes "wellformed \<Gamma>"
      and "p \<in> cterms \<Gamma>"
  obtains pn where "p \<in> ctermsl (\<Gamma> pn)"
               and "not_call p"
  using assms(2) unfolding cterms_def' [OF assms(1)] by auto

corollary cterms_subterms:
  assumes "wellformed \<Gamma>"
    shows "cterms \<Gamma> = {p|p pn. p\<in>subterms (\<Gamma> pn) \<and> not_call p \<and> not_choice p}"
  by (subst cterms_def' [OF assms(1)], subst ctermsl_subterms) auto

lemma subterms_in_cterms [elim]:
  assumes "wellformed \<Gamma>"
      and "p\<in>subterms (\<Gamma> pn)"
      and "not_call p"
      and "not_choice p"
    shows "p \<in> cterms \<Gamma>"
  using assms unfolding cterms_subterms [OF \<open>wellformed \<Gamma>\<close>] by auto

lemma subterms_stermsl_ctermsl:
  assumes "q \<in> subterms p"
      and "r \<in> stermsl q"
    shows "r \<in> ctermsl p"
  using assms
  proof (induct p)
    fix p1 p2
    assume IH1: "q \<in> subterms p1 \<Longrightarrow> r \<in> stermsl q \<Longrightarrow> r \<in> ctermsl p1"
       and IH2: "q \<in> subterms p2 \<Longrightarrow> r \<in> stermsl q \<Longrightarrow> r \<in> ctermsl p2"
       and *: "q \<in> subterms (p1 \<oplus> p2)"
       and "r \<in> stermsl q"
    from * have "q \<in> {p1 \<oplus> p2} \<union> subterms p1 \<union> subterms p2" by simp
    thus "r \<in> ctermsl (p1 \<oplus> p2)"
    proof (elim UnE)
      assume "q \<in> {p1 \<oplus> p2}" with \<open>r \<in> stermsl q\<close> show ?thesis
      by simp (metis stermsl_ctermsl)
    next
      assume "q \<in> subterms p1" hence "r \<in> ctermsl p1" using \<open>r \<in> stermsl q\<close> by (rule IH1)
      thus ?thesis by simp
    next
      assume "q \<in> subterms p2" hence "r \<in> ctermsl p2" using \<open>r \<in> stermsl q\<close> by (rule IH2)
      thus ?thesis by simp
    qed
  qed auto

lemma subterms_sterms_cterms:
  assumes wf: "wellformed \<Gamma>"
      and "p \<in> subterms (\<Gamma> pn)"
    shows "sterms \<Gamma> p \<subseteq> cterms \<Gamma>"
  using assms(2)
  proof (induct p)
    fix p
    assume "call(p) \<in> subterms (\<Gamma> pn)"
    from wf have "sterms \<Gamma> (call(p)) = sterms \<Gamma> (\<Gamma> p)" by simp
      thus "sterms \<Gamma> (call(p)) \<subseteq> cterms \<Gamma>" by auto
  next
    fix p1 p2
    assume IH1: "p1 \<in> subterms (\<Gamma> pn) \<Longrightarrow> sterms \<Gamma> p1 \<subseteq> cterms \<Gamma>"
       and IH2: "p2 \<in> subterms (\<Gamma> pn) \<Longrightarrow> sterms \<Gamma> p2 \<subseteq> cterms \<Gamma>"
       and *: "p1 \<oplus> p2 \<in> subterms (\<Gamma> pn)"
    from * have "p1 \<in> subterms (\<Gamma> pn)" by auto
    hence "sterms \<Gamma> p1 \<subseteq> cterms \<Gamma>" by (rule IH1)
    moreover from * have "p2 \<in> subterms (\<Gamma> pn)" by auto
      hence "sterms \<Gamma> p2 \<subseteq> cterms \<Gamma>" by (rule IH2)
    ultimately show "sterms \<Gamma> (p1 \<oplus> p2 ) \<subseteq> cterms \<Gamma>" using wf by simp
  qed (auto elim!: subterms_in_cterms [OF \<open>wellformed \<Gamma>\<close>])

lemma subterms_sterms_in_cterms:
  assumes "wellformed \<Gamma>"
      and "p \<in> subterms (\<Gamma> pn)"
      and "q \<in> sterms \<Gamma> p"
    shows "q \<in> cterms \<Gamma>"
  using assms
  by (auto dest!: subterms_sterms_cterms [OF \<open>wellformed \<Gamma>\<close>])

end
