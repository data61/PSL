(*  Title:       variants/e_all_abcd/Aodv_Loop_Freedom.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
*)

section "Lift and transfer invariants to show loop freedom"

theory E_Aodv_Loop_Freedom
imports AWN.OClosed_Transfer AWN.Qmsg_Lifting E_Global_Invariants E_Loop_Freedom
begin

subsection \<open>Lift to parallel processes with queues\<close>

lemma par_step_no_change_on_send_or_receive:
    fixes \<sigma> s a \<sigma>' s'
  assumes "((\<sigma>, s), a, (\<sigma>', s')) \<in> oparp_sos i (oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G)"
      and "a \<noteq> \<tau>"
    shows "\<sigma>' i = \<sigma> i"
  using assms by (rule qmsg_no_change_on_send_or_receive)

lemma par_nhop_quality_increases:
  shows "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile> (otherwith ((=)) {i} (orecvmsg (\<lambda>\<sigma> m.
                                    msg_fresh \<sigma> m \<and> msg_zhops m)),
                                  other quality_increases {i} \<rightarrow>)
                        global (\<lambda>\<sigma>. \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                          in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                                             \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
    proof (rule lift_into_qmsg [OF seq_nhop_quality_increases])
    show "opaodv i \<Turnstile>\<^sub>A (otherwith ((=)) {i}
                         (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)),
                        other quality_increases {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, _, \<sigma>'). quality_increases (\<sigma> i) (\<sigma>' i))"
    proof (rule ostep_invariant_weakenE [OF oquality_increases], simp_all)
      fix t :: "(((nat \<Rightarrow> state) \<times> (state, msg, pseqp, pseqp label) seqp), msg seq_action) transition"
      assume "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), _, (\<sigma>', _)). \<forall>j. quality_increases (\<sigma> j) (\<sigma>' j)) t"
      thus "quality_increases (fst (fst t) i) (fst (snd (snd t)) i)"
        by (cases t) (clarsimp dest!: onllD, metis aodv_ex_label)
    next
      fix \<sigma> \<sigma>' a
      assume "otherwith ((=)) {i}
                (orecvmsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)) \<sigma> \<sigma>' a"
      thus "otherwith quality_increases {i} (orecvmsg (\<lambda>_. rreq_rrep_sn)) \<sigma> \<sigma>' a"
        by - (erule weaken_otherwith, auto)
    qed
  qed auto

lemma par_rreq_rrep_sn_quality_increases:
  "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, _, \<sigma>'). quality_increases (\<sigma> i) (\<sigma>' i))"
  proof -
    have "opaodv i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                globala (\<lambda>(\<sigma>, _, \<sigma>'). quality_increases (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF olocal_quality_increases])
         (auto dest!: onllD seqllD elim!: aodv_ex_labelE)
    hence "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                   globala (\<lambda>(\<sigma>, _, \<sigma>'). quality_increases (\<sigma> i) (\<sigma>' i))"
      by (rule lift_step_into_qmsg_statelessassm) simp_all
    thus ?thesis by rule auto
  qed

lemma par_rreq_rrep_nsqn_fresh_any_step:
  shows "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>,
                                   other (\<lambda>_ _. True) {i} \<rightarrow>)
                                  globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (msg_fresh \<sigma>) a)"
  proof -
    have "opaodv i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. (orecvmsg (\<lambda>_. rreq_rrep_sn)) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                       globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (msg_fresh \<sigma>) a)"
    proof (rule ostep_invariant_weakenE [OF rreq_rrep_nsqn_fresh_any_step_invariant])
      fix t
      assume "onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<sigma>, _), a, _). anycast (msg_fresh \<sigma>) a) t"
      thus "globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (msg_fresh \<sigma>) a) t"
        by (cases t) (clarsimp dest!: onllD, metis aodv_ex_label)
    qed auto
    hence "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. (orecvmsg (\<lambda>_. rreq_rrep_sn)) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                    globala (\<lambda>(\<sigma>, a, \<sigma>'). anycast (msg_fresh \<sigma>) a)"
      by (rule lift_step_into_qmsg_statelessassm) simp_all
    thus ?thesis by rule auto
  qed

lemma par_anycast_msg_zhops:
  shows "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                  globala (\<lambda>(_, a, _). anycast msg_zhops a)"
  proof -
    from anycast_msg_zhops initiali_aodv oaodv_trans aodv_trans
      have "opaodv i \<Turnstile>\<^sub>A (act TT, other (\<lambda>_ _. True) {i} \<rightarrow>)
                         seqll i (onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(_, a, _). anycast msg_zhops a))"
        by (rule open_seq_step_invariant)
    hence "opaodv i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(_, a, _). anycast msg_zhops a)"
    proof (rule ostep_invariant_weakenE)
      fix t :: "(((nat \<Rightarrow> state) \<times> (state, msg, pseqp, pseqp label) seqp), msg seq_action) transition"
      assume "seqll i (onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(_, a, _). anycast msg_zhops a)) t"
      thus "globala (\<lambda>(_, a, _). anycast msg_zhops a) t"
        by (cases t) (clarsimp dest!: seqllD onllD, metis aodv_ex_label)
    qed simp_all
    hence "opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                     globala (\<lambda>(_, a, _). anycast msg_zhops a)"
      by (rule lift_step_into_qmsg_statelessassm) simp_all
    thus ?thesis by rule auto
  qed

subsection \<open>Lift to nodes\<close>

lemma node_step_no_change_on_send_or_receive:
  assumes "((\<sigma>, NodeS i P R), a, (\<sigma>', NodeS i' P' R')) \<in> onode_sos
                                      (oparp_sos i (oseqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i) (seqp_sos \<Gamma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G))"
      and "a \<noteq> \<tau>"
    shows "\<sigma>' i = \<sigma> i"
  using assms
  by (cases a) (auto elim!: par_step_no_change_on_send_or_receive)

lemma node_nhop_quality_increases:
  shows "\<langle> i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R \<rangle>\<^sub>o \<Turnstile>
           (otherwith ((=)) {i}
              (oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)),
              other quality_increases {i}
            \<rightarrow>) global (\<lambda>\<sigma>. \<forall>dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                  in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                                     \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
  by (rule node_lift [OF par_nhop_quality_increases]) auto

lemma node_quality_increases:
  "\<langle> i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R \<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma>,
                                         other (\<lambda>_ _. True) {i} \<rightarrow>)
                            globala (\<lambda>(\<sigma>, _, \<sigma>'). quality_increases (\<sigma> i) (\<sigma>' i))"
  by (rule node_lift_step_statelessassm [OF par_rreq_rrep_sn_quality_increases]) simp

lemma node_rreq_rrep_nsqn_fresh_any_step:
  shows "\<langle> i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R \<rangle>\<^sub>o \<Turnstile>\<^sub>A
          (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
          globala (\<lambda>(\<sigma>, a, \<sigma>'). castmsg (msg_fresh \<sigma>) a)"
  by (rule node_lift_anycast_statelessassm [OF par_rreq_rrep_nsqn_fresh_any_step])

lemma node_anycast_msg_zhops:
  shows "\<langle> i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R \<rangle>\<^sub>o \<Turnstile>\<^sub>A
          (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
          globala (\<lambda>(_, a, _). castmsg msg_zhops a)"
  by (rule node_lift_anycast_statelessassm [OF par_anycast_msg_zhops])

lemma node_silent_change_only:
  shows "\<langle> i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i \<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_ _. True) \<sigma>,
                                               other (\<lambda>_ _. True) {i} \<rightarrow>)
          globala (\<lambda>(\<sigma>, a, \<sigma>'). a \<noteq> \<tau> \<longrightarrow> \<sigma>' i = \<sigma> i)"
  proof (rule ostep_invariantI, simp (no_asm), rule impI)
    fix \<sigma> \<zeta> a \<sigma>' \<zeta>'
    assume or: "(\<sigma>, \<zeta>) \<in> oreachable (\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o)
                                    (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_ _. True) \<sigma>)
                                    (other (\<lambda>_ _. True) {i})"
      and tr: "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> trans (\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o)"
      and "a \<noteq> \<tau>\<^sub>n"
    from or obtain p R where "\<zeta> = NodeS i p R"
      by - (drule node_net_state, metis)
    with tr have "((\<sigma>, NodeS i p R), a, (\<sigma>', \<zeta>'))
                     \<in> onode_sos (oparp_sos i (trans (opaodv i)) (trans qmsg))"
      by simp
    thus "\<sigma>' i = \<sigma> i" using \<open>a \<noteq> \<tau>\<^sub>n\<close> 
      by (cases rule: onode_sos.cases)
         (auto elim: qmsg_no_change_on_send_or_receive)
  qed

subsection \<open>Lift to partial networks\<close>

lemma arrive_rreq_rrep_nsqn_fresh_inc_sn [simp]:
  assumes "oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> P \<sigma> m) \<sigma> m"
    shows "oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma> m"
  using assms by (cases m) auto

lemma opnet_nhop_quality_increases:
  shows "opnet (\<lambda>i. opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) p \<Turnstile>
           (otherwith ((=)) (net_tree_ips p)
              (oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)),
               other quality_increases (net_tree_ips p) \<rightarrow>)
              global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips p. \<forall>dip.
                          let nhip = the (nhop (rt (\<sigma> i)) dip)
                          in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                             \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
  proof (rule pnet_lift [OF node_nhop_quality_increases])
    fix i R
    have "\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma>,
                                              other (\<lambda>_ _. True) {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, \<sigma>').
            castmsg (\<lambda>m. msg_fresh \<sigma> m \<and> msg_zhops m) a)"
    proof (rule ostep_invariantI, simp (no_asm))
      fix \<sigma> s a \<sigma>' s'
      assume or: "(\<sigma>, s) \<in> oreachable (\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o)
                                      (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma>)
                                      (other (\<lambda>_ _. True) {i})"
         and tr: "((\<sigma>, s), a, (\<sigma>', s')) \<in> trans (\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o)"
         and am: "oarrivemsg (\<lambda>_. rreq_rrep_sn) \<sigma> a"
      from or tr am have "castmsg (msg_fresh \<sigma>) a"
        by (auto dest!: ostep_invariantD [OF node_rreq_rrep_nsqn_fresh_any_step])
      moreover from or tr am have "castmsg (msg_zhops) a"
        by (auto dest!: ostep_invariantD [OF node_anycast_msg_zhops])
      ultimately show "castmsg (\<lambda>m. msg_fresh \<sigma> m \<and> msg_zhops m) a"
        by (case_tac a) auto
    qed
    thus "\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A
            (\<lambda>\<sigma> _. oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m) \<sigma>,
             other quality_increases {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, _).
               castmsg (\<lambda>m. msg_fresh \<sigma> m \<and> msg_zhops m) a)"
      by rule auto
  next
    fix i R
    show "\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A
            (\<lambda>\<sigma> _. oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m) \<sigma>,
             other quality_increases {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, \<sigma>').
               a \<noteq> \<tau> \<and> (\<forall>d. a \<noteq> i:deliver(d)) \<longrightarrow> \<sigma> i = \<sigma>' i)"
      by (rule ostep_invariant_weakenE [OF node_silent_change_only]) auto
  next
    fix i R
    show "\<langle>i : opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A
            (\<lambda>\<sigma> _. oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m) \<sigma>,
             other quality_increases {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, \<sigma>').
               a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> quality_increases (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF node_quality_increases]) auto
  qed simp_all

subsection \<open>Lift to closed networks\<close>

lemma onet_nhop_quality_increases:
  shows "oclosed (opnet (\<lambda>i. opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) p)
           \<Turnstile> (\<lambda>_ _ _. True, other quality_increases (net_tree_ips p) \<rightarrow>)
              global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips p. \<forall>dip.
                          let nhip = the (nhop (rt (\<sigma> i)) dip)
                          in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                             \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
  (is "_ \<Turnstile> (_, ?U \<rightarrow>) ?inv")
  proof (rule inclosed_closed)
    from opnet_nhop_quality_increases
      show "opnet (\<lambda>i. opaodv i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) p
               \<Turnstile> (otherwith ((=)) (net_tree_ips p) inoclosed, ?U \<rightarrow>) ?inv"
    proof (rule oinvariant_weakenE)
      fix \<sigma> \<sigma>' :: "ip \<Rightarrow> state" and a :: "msg node_action"
      assume "otherwith ((=)) (net_tree_ips p) inoclosed \<sigma> \<sigma>' a"
      thus "otherwith ((=)) (net_tree_ips p)
              (oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m)) \<sigma> \<sigma>' a"
      proof (rule otherwithEI)
        fix \<sigma> :: "ip \<Rightarrow> state" and a :: "msg node_action"
        assume "inoclosed \<sigma> a"
        thus "oarrivemsg (\<lambda>\<sigma> m. msg_fresh \<sigma> m \<and> msg_zhops m) \<sigma> a"
        proof (cases a)
          fix ii ni ms
          assume "a = ii\<not>ni:arrive(ms)"
          moreover with \<open>inoclosed \<sigma> a\<close> obtain d di where "ms = newpkt(d, di)"
            by (cases ms) auto
          ultimately show ?thesis by simp
        qed simp_all
      qed
    qed
  qed

subsection \<open>Transfer into the standard model\<close>

interpretation aodv_openproc: openproc paodv opaodv id
  rewrites "aodv_openproc.initmissing = initmissing"
  proof -
    show "openproc paodv opaodv id"
    proof unfold_locales
      fix i :: ip
      have "{(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i \<and> (\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> fst ` \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V j)} \<subseteq> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'"
        unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V'_def
        proof (rule equalityD1)
          show "\<And>f p. {(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> {(f i, p)} \<and> (\<forall>j. j \<noteq> i
                      \<longrightarrow> \<sigma> j \<in> fst ` {(f j, p)})} = {(f, p)}"
            by (rule set_eqI) auto
        qed
      thus "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (paodv i)
                             \<and> (\<sigma> i, \<zeta>) = id s
                             \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o id) ` init (paodv j)) } \<subseteq> init (opaodv i)"
        by simp
    next
      show "\<forall>j. init (paodv j) \<noteq> {}"
        unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by simp
    next
      fix i s a s' \<sigma> \<sigma>'
      assume "\<sigma> i = fst (id s)"
         and "\<sigma>' i = fst (id s')"
         and "(s, a, s') \<in> trans (paodv i)"
      then obtain q q' where "s = (\<sigma> i, q)"
                         and "s' = (\<sigma>' i, q')"
                         and "((\<sigma> i, q), a, (\<sigma>' i, q')) \<in> trans (paodv i)" 
         by (cases s, cases s') auto
      from this(3) have "((\<sigma>, q), a, (\<sigma>', q')) \<in> trans (opaodv i)"
        by simp (rule open_seqp_action [OF aodv_wf])

      with \<open>s = (\<sigma> i, q)\<close> and \<open>s' = (\<sigma>' i, q')\<close>
        show "((\<sigma>, snd (id s)), a, (\<sigma>', snd (id s'))) \<in> trans (opaodv i)"
          by simp
    qed
    then interpret opn: openproc paodv opaodv id .
    have [simp]: "\<And>i. (SOME x. x \<in> (fst o id) ` init (paodv i)) = aodv_init i"
      unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by simp
    hence "\<And>i. openproc.initmissing paodv id i = initmissing i"
      unfolding opn.initmissing_def opn.someinit_def initmissing_def
      by (auto split: option.split)
    thus "openproc.initmissing paodv id = initmissing" ..
  qed

interpretation aodv_openproc_par_qmsg: openproc_parq paodv opaodv id qmsg
  rewrites "aodv_openproc_par_qmsg.netglobal = netglobal"
    and "aodv_openproc_par_qmsg.initmissing = initmissing"
  proof -
    show "openproc_parq paodv opaodv id qmsg"
      by (unfold_locales) simp
    then interpret opq: openproc_parq paodv opaodv id qmsg .

    have im: "\<And>\<sigma>. openproc.initmissing (\<lambda>i. paodv i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) \<sigma>
                                                                                    = initmissing \<sigma>"
      unfolding opq.initmissing_def opq.someinit_def initmissing_def
      unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by (clarsimp cong: option.case_cong)
    thus "openproc.initmissing (\<lambda>i. paodv i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) = initmissing"
      by (rule ext)
    have "\<And>P \<sigma>. openproc.netglobal (\<lambda>i. paodv i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) P \<sigma>
                                                                                = netglobal P \<sigma>"
      unfolding opq.netglobal_def netglobal_def opq.initmissing_def initmissing_def opq.someinit_def
      unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def
      by (clarsimp cong: option.case_cong
                   simp del: One_nat_def
                   simp add: fst_initmissing_netgmap_default_aodv_init_netlift
                                                  [symmetric, unfolded initmissing_def])
    thus "openproc.netglobal (\<lambda>i. paodv i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (id p), snd (id p), q)) = netglobal"
      by auto
  qed

lemma net_nhop_quality_increases:
  assumes "wf_net_tree n"
  shows "closed (pnet (\<lambda>i. paodv i \<langle>\<langle> qmsg) n) \<TTurnstile> netglobal
                           (\<lambda>\<sigma>. \<forall>i dip. let nhip = the (nhop (rt (\<sigma> i)) dip)
                                        in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                                            \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
        (is "_ \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i. ?inv \<sigma> i)")
  proof -
    from \<open>wf_net_tree n\<close>
      have proto: "closed (pnet (\<lambda>i. paodv i \<langle>\<langle> qmsg) n) \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. \<forall>dip.
                                            let nhip = the (nhop (rt (\<sigma> i)) dip)
                                            in dip \<in> vD (rt (\<sigma> i)) \<inter> vD (rt (\<sigma> nhip)) \<and> nhip \<noteq> dip
                                                \<longrightarrow> (rt (\<sigma> i)) \<sqsubset>\<^bsub>dip\<^esub> (rt (\<sigma> nhip)))"
        by (rule aodv_openproc_par_qmsg.close_opnet [OF _ onet_nhop_quality_increases])
    show ?thesis
    unfolding invariant_def opnet_sos.opnet_tau1
    proof (rule, simp only: aodv_openproc_par_qmsg.netglobalsimp
                            fst_initmissing_netgmap_pair_fst, rule allI)
      fix \<sigma> i
      assume sr: "\<sigma> \<in> reachable (closed (pnet (\<lambda>i. paodv i \<langle>\<langle> qmsg) n)) TT"
      hence "\<forall>i\<in>net_tree_ips n. ?inv (fst (initmissing (netgmap fst \<sigma>))) i"
        by - (drule invariantD [OF proto],
              simp only: aodv_openproc_par_qmsg.netglobalsimp
                         fst_initmissing_netgmap_pair_fst)
      thus "?inv (fst (initmissing (netgmap fst \<sigma>))) i"
      proof (cases "i\<in>net_tree_ips n")
        assume "i\<notin>net_tree_ips n"
        from sr have "\<sigma> \<in> reachable (pnet (\<lambda>i. paodv i \<langle>\<langle> qmsg) n) TT" ..
        hence "net_ips \<sigma> = net_tree_ips n" ..
        with \<open>i\<notin>net_tree_ips n\<close> have "i\<notin>net_ips \<sigma>" by simp
        hence "(fst (initmissing (netgmap fst \<sigma>))) i = aodv_init i"
          by simp
        thus ?thesis by simp
      qed metis
    qed
  qed

subsection \<open>Loop freedom of AODV\<close>

theorem aodv_loop_freedom:
  assumes "wf_net_tree n"
  shows "closed (pnet (\<lambda>i. paodv i \<langle>\<langle> qmsg) n) \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>dip. irrefl ((rt_graph \<sigma> dip)\<^sup>+))"
  using assms by (rule aodv_openproc_par_qmsg.netglobal_weakenE
                          [OF net_nhop_quality_increases inv_to_loop_freedom])

end
