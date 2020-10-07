(*  Title:       AWN_SOS.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Semantics of the Algebra of Wireless Networks"

theory AWN_SOS
imports TransitionSystems AWN
begin

subsection "Table 1: Structural operational semantics for sequential process expressions "

inductive_set
  seqp_sos
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ('s \<times> ('s, 'm, 'p, 'l) seqp, 'm seq_action) transition set"
  for \<Gamma> :: "('s, 'm, 'p, 'l) seqp_env"
where
    broadcastT: "((\<xi>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g).p),          broadcast (s\<^sub>m\<^sub>s\<^sub>g \<xi>),         (\<xi>, p)) \<in> seqp_sos \<Gamma>"
  | groupcastT: "((\<xi>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g).p),    groupcast (s\<^sub>i\<^sub>p\<^sub>s \<xi>) (s\<^sub>m\<^sub>s\<^sub>g \<xi>), (\<xi>, p)) \<in> seqp_sos \<Gamma>"
  | unicastT:   "((\<xi>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q),   unicast (s\<^sub>i\<^sub>p \<xi>) (s\<^sub>m\<^sub>s\<^sub>g \<xi>),    (\<xi>, p)) \<in> seqp_sos \<Gamma>"
  | notunicastT:"((\<xi>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q),    \<not>unicast (s\<^sub>i\<^sub>p \<xi>),          (\<xi>, q)) \<in> seqp_sos \<Gamma>"
  | sendT:      "((\<xi>, {l}send(s\<^sub>m\<^sub>s\<^sub>g).p),               send (s\<^sub>m\<^sub>s\<^sub>g \<xi>),              (\<xi>, p)) \<in> seqp_sos \<Gamma>"
  | deliverT:   "((\<xi>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a).p),           deliver (s\<^sub>d\<^sub>a\<^sub>t\<^sub>a \<xi>),          (\<xi>, p)) \<in> seqp_sos \<Gamma>"
  | receiveT:   "((\<xi>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g).p),            receive msg,       (u\<^sub>m\<^sub>s\<^sub>g msg \<xi>, p)) \<in> seqp_sos \<Gamma>"
  | assignT:    "((\<xi>, {l}\<lbrakk>u\<rbrakk> p),                      \<tau>,                        (u \<xi>, p)) \<in> seqp_sos \<Gamma>"

  | callT:      "\<lbrakk> ((\<xi>, \<Gamma> pn), a, (\<xi>', p')) \<in> seqp_sos \<Gamma> \<rbrakk> \<Longrightarrow>
                 ((\<xi>, call(pn)), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>" (* TPB: quite different to Table 1 *)

  | choiceT1:   "((\<xi>, p), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>  \<Longrightarrow> ((\<xi>, p \<oplus> q), a, (\<xi>', p')) \<in> seqp_sos \<Gamma>"
  | choiceT2:   "((\<xi>, q), a, (\<xi>', q')) \<in> seqp_sos \<Gamma>  \<Longrightarrow> ((\<xi>, p \<oplus> q), a, (\<xi>', q')) \<in> seqp_sos \<Gamma>"

  | guardT:     "\<xi>' \<in> g \<xi> \<Longrightarrow> ((\<xi>, {l}\<langle>g\<rangle> p), \<tau>, (\<xi>', p)) \<in> seqp_sos \<Gamma>"

inductive_cases
      seqp_callTE [elim]:      "((\<xi>, call(pn)), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"
  and seqp_choiceTE [elim]:    "((\<xi>, p1 \<oplus> p2), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>"

lemma seqp_broadcastTE [elim]:
  "\<lbrakk>((\<xi>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
    \<lbrakk>a = broadcast (s\<^sub>m\<^sub>s\<^sub>g \<xi>); \<xi>' = \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_groupcastTE [elim]:
  "\<lbrakk>((\<xi>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
    \<lbrakk>a = groupcast (s\<^sub>i\<^sub>p\<^sub>s \<xi>) (s\<^sub>m\<^sub>s\<^sub>g \<xi>); \<xi>' = \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_unicastTE [elim]:
  "\<lbrakk>((\<xi>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q), a, (\<xi>', r)) \<in> seqp_sos \<Gamma>;
    \<lbrakk>a = unicast (s\<^sub>i\<^sub>p \<xi>) (s\<^sub>m\<^sub>s\<^sub>g \<xi>); \<xi>' = \<xi>; r = p\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>a = \<not>unicast (s\<^sub>i\<^sub>p \<xi>); \<xi>' = \<xi>; r = q\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q), a, (\<xi>', r)) \<in> seqp_sos \<Gamma>") simp_all

lemma seqp_sendTE [elim]:
  "\<lbrakk>((\<xi>, {l}send(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
    \<lbrakk>a = send (s\<^sub>m\<^sub>s\<^sub>g \<xi>); \<xi>' = \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}send(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_deliverTE [elim]:
  "\<lbrakk>((\<xi>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
    \<lbrakk>a = deliver (s\<^sub>d\<^sub>a\<^sub>t\<^sub>a \<xi>); \<xi>' = \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_receiveTE [elim]:
  "\<lbrakk>((\<xi>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>;
    \<And>msg. \<lbrakk>a = receive msg; \<xi>' = u\<^sub>m\<^sub>s\<^sub>g msg \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g). p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_assignTE [elim]:
  "\<lbrakk>((\<xi>, {l}\<lbrakk>u\<rbrakk> p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>; \<lbrakk>a = \<tau>; \<xi>' = u \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}\<lbrakk>u\<rbrakk> p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemma seqp_guardTE [elim]:
  "\<lbrakk>((\<xi>, {l}\<langle>g\<rangle> p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>; \<lbrakk>a = \<tau>; \<xi>' \<in> g \<xi>; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<xi>, {l}\<langle>g\<rangle> p), a, (\<xi>', q)) \<in> seqp_sos \<Gamma>") simp

lemmas seqpTEs =
  seqp_broadcastTE
  seqp_groupcastTE
  seqp_unicastTE
  seqp_sendTE
  seqp_deliverTE
  seqp_receiveTE
  seqp_assignTE
  seqp_callTE
  seqp_choiceTE
  seqp_guardTE

declare seqp_sos.intros [intro]

subsection "Table 2: Structural operational semantics for parallel process expressions "

inductive_set
  parp_sos :: "('s1, 'm seq_action) transition set
                    \<Rightarrow> ('s2, 'm seq_action) transition set
                    \<Rightarrow> ('s1 \<times> 's2, 'm seq_action) transition set"
  for S :: "('s1, 'm seq_action) transition set"
  and T :: "('s2, 'm seq_action) transition set"
where
    parleft:  "\<lbrakk> (s, a, s') \<in> S; \<And>m. a \<noteq> receive m \<rbrakk> \<Longrightarrow> ((s, t), a, (s', t)) \<in> parp_sos S T"
  | parright: "\<lbrakk> (t, a, t') \<in> T; \<And>m. a \<noteq> send m \<rbrakk> \<Longrightarrow> ((s, t), a, (s, t')) \<in> parp_sos S T"
  | parboth:  "\<lbrakk> (s, receive m, s') \<in> S; (t, send m, t') \<in> T \<rbrakk>
               \<Longrightarrow>((s, t), \<tau>, (s', t')) \<in> parp_sos S T"

lemma par_broadcastTE [elim]:
  "\<lbrakk>((s, t), broadcast m, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, broadcast m, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, broadcast m, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), broadcast m, (s', t')) \<in> parp_sos S T") simp_all

lemma par_groupcastTE [elim]:
  "\<lbrakk>((s, t), groupcast ips m, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, groupcast ips m, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, groupcast ips m, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), groupcast ips m, (s', t')) \<in> parp_sos S T") simp_all

lemma par_unicastTE [elim]:
  "\<lbrakk>((s, t), unicast i m, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, unicast i m, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, unicast i m, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), unicast i m, (s', t')) \<in> parp_sos S T") simp_all

lemma par_notunicastTE [elim]:
  "\<lbrakk>((s, t), notunicast i, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, notunicast i, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, notunicast i, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), notunicast i, (s', t')) \<in> parp_sos S T") simp_all

lemma par_sendTE [elim]:
  "\<lbrakk>((s, t), send m, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, send m, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), send m, (s', t')) \<in> parp_sos S T") auto

lemma par_deliverTE [elim]:
  "\<lbrakk>((s, t), deliver d, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(s, deliver d, s') \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, deliver d, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), deliver d, (s', t')) \<in> parp_sos S T") simp_all

lemma par_receiveTE [elim]:
  "\<lbrakk>((s, t), receive m, (s', t')) \<in> parp_sos S T;
    \<lbrakk>(t, receive m, t') \<in> T; s' = s\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((s, t), receive m, (s', t')) \<in> parp_sos S T") auto

inductive_cases par_tauTE: "((s, t), \<tau>, (s', t')) \<in> parp_sos S T"

lemmas parpTEs =
  par_broadcastTE
  par_groupcastTE
  par_unicastTE
  par_notunicastTE
  par_sendTE
  par_deliverTE
  par_receiveTE

lemma parp_sos_cases [elim]:
  assumes "((s, t), a, (s', t')) \<in> parp_sos S T"
      and "\<lbrakk> (s, a, s') \<in> S; \<And>m. a \<noteq> receive m; t' = t \<rbrakk> \<Longrightarrow> P"
      and "\<lbrakk> (t, a, t') \<in> T; \<And>m. a \<noteq> send m; s' = s \<rbrakk> \<Longrightarrow> P"
      and "\<And>m. \<lbrakk> (s, receive m, s') \<in> S; (t, send m, t') \<in> T \<rbrakk> \<Longrightarrow> P"
    shows "P"
  using assms by cases auto

definition
  par_comp :: "('s1, 'm seq_action) automaton
              \<Rightarrow> ('s2, 'm seq_action) automaton
              \<Rightarrow> ('s1 \<times> 's2, 'm seq_action) automaton"
  ("(_ \<langle>\<langle> _)" [102, 103] 102)
where
  "s \<langle>\<langle> t \<equiv> \<lparr> init = init s \<times> init t, trans = parp_sos (trans s) (trans t) \<rparr>"

lemma trans_par_comp [simp]:
  "trans (s \<langle>\<langle> t) = parp_sos (trans s) (trans t)"
  unfolding par_comp_def by simp

lemma init_par_comp [simp]:
  "init (s \<langle>\<langle> t) = init s \<times> init t"
  unfolding par_comp_def by simp

subsection "Table 3: Structural operational semantics for node expressions "

inductive_set
  node_sos :: "('s, 'm seq_action) transition set \<Rightarrow> ('s net_state, 'm node_action) transition set"
  for S :: "('s, 'm seq_action) transition set"
where
    node_bcast:
    "(s, broadcast m, s') \<in> S \<Longrightarrow> (NodeS i s R, R:*cast(m), NodeS i s' R) \<in> node_sos S"
  | node_gcast:
    "(s, groupcast D m, s') \<in> S \<Longrightarrow> (NodeS i s R, (R\<inter>D):*cast(m), NodeS i s' R) \<in> node_sos S"
  | node_ucast:
    "\<lbrakk> (s, unicast d m, s') \<in> S; d\<in>R \<rbrakk> \<Longrightarrow> (NodeS i s R, {d}:*cast(m), NodeS i s' R) \<in> node_sos S"
  | node_notucast:
    "\<lbrakk> (s, \<not>unicast d, s') \<in> S; d\<notin>R \<rbrakk> \<Longrightarrow> (NodeS i s R, \<tau>, NodeS i s' R) \<in> node_sos S"
  | node_deliver:
    "(s, deliver d, s') \<in> S \<Longrightarrow> (NodeS i s R, i:deliver(d), NodeS i s' R) \<in> node_sos S"
  | node_receive:
    "(s, receive m, s') \<in> S \<Longrightarrow> (NodeS i s R, {i}\<not>{}:arrive(m), NodeS i s' R) \<in> node_sos S"
  | node_tau:
    "(s, \<tau>, s') \<in> S         \<Longrightarrow> (NodeS i s R, \<tau>, NodeS i s' R) \<in> node_sos S"
  | node_arrive:
    "(NodeS i s R, {}\<not>{i}:arrive(m),  NodeS i s R) \<in> node_sos S"
  | node_connect1:
    "(NodeS i s R, connect(i, i'),    NodeS i s (R \<union> {i'})) \<in> node_sos S"
  | node_connect2:
    "(NodeS i s R, connect(i', i),    NodeS i s (R \<union> {i'})) \<in> node_sos S"
  | node_disconnect1:
    "(NodeS i s R, disconnect(i, i'), NodeS i s (R - {i'})) \<in> node_sos S"
  | node_disconnect2:
    "(NodeS i s R, disconnect(i', i), NodeS i s (R - {i'})) \<in> node_sos S"
  | node_connect_other:
    "\<lbrakk> i \<noteq> i'; i \<noteq> i'' \<rbrakk> \<Longrightarrow> (NodeS i s R, connect(i', i''), NodeS i s R) \<in> node_sos S"
  | node_disconnect_other:
    "\<lbrakk> i \<noteq> i'; i \<noteq> i'' \<rbrakk> \<Longrightarrow> (NodeS i s R, disconnect(i', i''), NodeS i s R) \<in> node_sos S"

inductive_cases node_arriveTE:  "(NodeS i s R, ii\<not>ni:arrive(m), NodeS i s' R) \<in> node_sos S"
            and node_arriveTE': "(NodeS i s R, H\<not>K:arrive(m), s') \<in> node_sos S"
            and node_castTE:    "(NodeS i s R, RM:*cast(m), NodeS i s' R') \<in> node_sos S"
            and node_castTE':   "(NodeS i s R, RM:*cast(m), s') \<in> node_sos S"
            and node_deliverTE: "(NodeS i s R, i:deliver(d), NodeS i s' R) \<in> node_sos S"
            and node_deliverTE': "(s, i:deliver(d), s') \<in> node_sos S"
            and node_deliverTE'': "(NodeS ii s R, i:deliver(d), s') \<in> node_sos S"
            and node_tauTE:     "(NodeS i s R, \<tau>, NodeS i s' R) \<in> node_sos S"
            and node_tauTE':    "(NodeS i s R, \<tau>, s') \<in> node_sos S"
            and node_connectTE: "(NodeS ii s R, connect(i, i'), NodeS ii s' R') \<in> node_sos S"
            and node_connectTE': "(NodeS ii s R, connect(i, i'), s') \<in> node_sos S"
            and node_disconnectTE: "(NodeS ii s R, disconnect(i, i'), NodeS ii s' R') \<in> node_sos S"
            and node_disconnectTE': "(NodeS ii s R, disconnect(i, i'), s') \<in> node_sos S"

lemma node_sos_never_newpkt [simp]:
  assumes "(s, a, s') \<in> node_sos S"
    shows "a \<noteq> i:newpkt(d, di)"
  using assms by cases auto

lemma arrives_or_not:
  assumes "(NodeS i s R, ii\<not>ni:arrive(m), NodeS i' s' R') \<in> node_sos S"
    shows "(ii = {i} \<and> ni = {}) \<or> (ii = {} \<and> ni = {i})"
  using assms by rule simp_all

definition
  node_comp :: "ip \<Rightarrow> ('s, 'm seq_action) automaton \<Rightarrow> ip set
                   \<Rightarrow> ('s net_state, 'm node_action) automaton"
    ("(\<langle>_ : (_) : _\<rangle>)" [0, 0, 0] 104)
where
  "\<langle>i : np : R\<^sub>i\<rangle> \<equiv> \<lparr> init = {NodeS i s R\<^sub>i|s. s \<in> init np}, trans = node_sos (trans np) \<rparr>"

lemma trans_node_comp:
  "trans (\<langle>i : np : R\<^sub>i\<rangle>) = node_sos (trans np)"
  unfolding node_comp_def by simp

lemma init_node_comp:
  "init (\<langle>i : np : R\<^sub>i\<rangle>) = {NodeS i s R\<^sub>i|s. s \<in> init np}"
  unfolding node_comp_def by simp

lemmas node_comps = trans_node_comp init_node_comp

lemma trans_par_node_comp [simp]:
  "trans (\<langle>i : s \<langle>\<langle> t : R\<rangle>) = node_sos (parp_sos (trans s) (trans t))"
  unfolding node_comp_def by simp

lemma snd_par_node_comp [simp]:
  "init (\<langle>i : s \<langle>\<langle> t : R\<rangle>) = {NodeS i st R|st. st \<in> init s \<times> init t}"
  unfolding node_comp_def by simp

lemma node_sos_dest_is_net_state:
  assumes "(s, a, s') \<in> node_sos S"
    shows "\<exists>i' P' R'. s' = NodeS i' P' R'"
  using assms by induct auto

lemma node_sos_dest:
  assumes "(NodeS i p R, a, s') \<in> node_sos S"
    shows "\<exists>P' R'. s' = NodeS i P' R'"
  using assms assms [THEN node_sos_dest_is_net_state]
  by - (erule node_sos.cases, auto)

lemma node_sos_states [elim]:
  assumes "(ns, a, ns') \<in> node_sos S"
  obtains i s R s' R' where "ns  = NodeS i s  R"
                        and "ns' = NodeS i s' R'"
  proof -
    assume [intro!]: "\<And>i s R s' R'. ns = NodeS i s R \<Longrightarrow> ns' = NodeS i s' R' \<Longrightarrow> thesis"
    from assms(1) obtain i s R where "ns = NodeS i s R"
      by (cases ns) auto
    moreover with assms(1) obtain s' R' where "ns' = NodeS i s' R'"
      by (metis node_sos_dest)
    ultimately show thesis ..
  qed

lemma node_sos_cases [elim]:
  "(NodeS i p R, a, NodeS i p' R') \<in> node_sos S \<Longrightarrow>
  (\<And>m .       \<lbrakk> a = R:*cast(m);          R' = R; (p, broadcast m, p') \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m D.      \<lbrakk> a = (R \<inter> D):*cast(m);    R' = R; (p, groupcast D m, p') \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d m.      \<lbrakk> a = {d}:*cast(m);        R' = R; (p, unicast d m, p') \<in> S; d \<in> R \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d.        \<lbrakk> a = \<tau>;                   R' = R; (p, \<not>unicast d, p') \<in> S; d \<notin> R \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d.        \<lbrakk> a = i:deliver(d);        R' = R; (p, deliver d, p') \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m.        \<lbrakk> a = {i}\<not>{}:arrive(m);    R' = R; (p, receive m, p') \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (            \<lbrakk> a = \<tau>;                   R' = R; (p, \<tau>, p') \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m.        \<lbrakk> a = {}\<not>{i}:arrive(m);    R' = R; p = p' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = connect(i, i');      R' = R \<union> {i'}; p = p' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = connect(i', i);      R' = R \<union> {i'}; p = p' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = disconnect(i, i');   R' = R - {i'}; p = p' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = disconnect(i', i);   R' = R - {i'}; p = p' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i' i''. \<lbrakk> a = connect(i', i'');    R' = R; p = p'; i \<noteq> i'; i \<noteq> i'' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i' i''. \<lbrakk> a = disconnect(i', i''); R' = R; p = p'; i \<noteq> i'; i \<noteq> i'' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  P"
  by (erule node_sos.cases) simp_all

subsection "Table 4: Structural operational semantics for partial network expressions "

inductive_set
  pnet_sos :: "('s net_state, 'm node_action) transition set
                    \<Rightarrow> ('s net_state, 'm node_action) transition set
                    \<Rightarrow> ('s net_state, 'm node_action) transition set"
  for S :: "('s net_state, 'm node_action) transition set"
  and T :: "('s net_state, 'm node_action) transition set"
where
    pnet_cast1: "\<lbrakk> (s, R:*cast(m), s') \<in> S; (t, H\<not>K:arrive(m), t') \<in> T; H \<subseteq> R; K \<inter> R = {} \<rbrakk>
      \<Longrightarrow> (SubnetS s t, R:*cast(m), SubnetS s' t') \<in> pnet_sos S T"

  | pnet_cast2: "\<lbrakk> (s, H\<not>K:arrive(m), s') \<in> S; (t, R:*cast(m), t') \<in> T;  H \<subseteq> R; K \<inter> R = {} \<rbrakk>
      \<Longrightarrow> (SubnetS s t, R:*cast(m), SubnetS s' t') \<in> pnet_sos S T"

  | pnet_arrive: "\<lbrakk> (s, H\<not>K:arrive(m), s') \<in> S; (t, H'\<not>K':arrive(m), t') \<in> T \<rbrakk>
      \<Longrightarrow> (SubnetS s t,  (H \<union> H')\<not>(K \<union> K'):arrive(m), SubnetS s' t') \<in> pnet_sos S T"

  | pnet_deliver1: "(s, i:deliver(d), s') \<in> S
      \<Longrightarrow> (SubnetS s t, i:deliver(d), SubnetS s' t) \<in> pnet_sos S T"
  | pnet_deliver2: "\<lbrakk> (t, i:deliver(d), t') \<in> T \<rbrakk>
      \<Longrightarrow> (SubnetS s t, i:deliver(d), SubnetS s t') \<in> pnet_sos S T"

  | pnet_tau1: "(s, \<tau>, s') \<in> S \<Longrightarrow> (SubnetS s t, \<tau>, SubnetS s' t) \<in> pnet_sos S T"
  | pnet_tau2: "(t, \<tau>, t') \<in> T \<Longrightarrow> (SubnetS s t, \<tau>, SubnetS s t') \<in> pnet_sos S T"

  | pnet_connect: "\<lbrakk> (s, connect(i, i'), s') \<in> S; (t, connect(i, i'), t') \<in> T \<rbrakk>
      \<Longrightarrow> (SubnetS s t, connect(i, i'), SubnetS s' t') \<in> pnet_sos S T"

  | pnet_disconnect: "\<lbrakk> (s, disconnect(i, i'), s') \<in> S; (t, disconnect(i, i'), t') \<in> T \<rbrakk>
      \<Longrightarrow> (SubnetS s t, disconnect(i, i'), SubnetS s' t') \<in> pnet_sos S T"

inductive_cases partial_castTE [elim]:       "(s, R:*cast(m), s') \<in> pnet_sos S T"
            and partial_arriveTE [elim]:     "(s, H\<not>K:arrive(m), s') \<in> pnet_sos S T"
            and partial_deliverTE [elim]:    "(s, i:deliver(d), s') \<in> pnet_sos S T"
            and partial_tauTE [elim]:        "(s, \<tau>, s') \<in> pnet_sos S T"
            and partial_connectTE [elim]:    "(s, connect(i, i'), s') \<in> pnet_sos S T"
            and partial_disconnectTE [elim]: "(s, disconnect(i, i'), s') \<in> pnet_sos S T"

lemma pnet_sos_never_newpkt:
  assumes "(st, a, st') \<in> pnet_sos S T"
      and "\<And>i d di a s s'. (s, a, s') \<in> S \<Longrightarrow> a \<noteq> i:newpkt(d, di)"
      and "\<And>i d di a t t'. (t, a, t') \<in> T \<Longrightarrow> a \<noteq> i:newpkt(d, di)"
    shows "a \<noteq> i:newpkt(d, di)"
  using assms(1) by cases (auto dest!: assms(2-3))

fun pnet :: "(ip \<Rightarrow> ('s, 'm seq_action) automaton)
              \<Rightarrow> net_tree \<Rightarrow> ('s net_state, 'm node_action) automaton"
where
    "pnet np (\<langle>i; R\<^sub>i\<rangle>)  =  \<langle>i : np i : R\<^sub>i\<rangle>"
  | "pnet np (p\<^sub>1 \<parallel> p\<^sub>2) = \<lparr> init = {SubnetS s\<^sub>1 s\<^sub>2 |s\<^sub>1 s\<^sub>2. s\<^sub>1 \<in> init (pnet np p\<^sub>1)
                                                      \<and> s\<^sub>2 \<in> init (pnet np p\<^sub>2)},
                           trans = pnet_sos (trans (pnet np p\<^sub>1)) (trans (pnet np p\<^sub>2)) \<rparr>"

lemma pnet_node_init [elim, simp]:
  assumes "s \<in> init (pnet np \<langle>i; R\<rangle>)"
    shows "s \<in> { NodeS i s R |s. s \<in> init (np i)}"
  using assms by (simp add: node_comp_def)

lemma pnet_node_init' [elim]:
 assumes "s \<in> init (pnet np \<langle>i; R\<rangle>)"
 obtains ns where "s = NodeS i ns R"
             and "ns \<in> init (np i)"
   using assms by (auto simp add: node_comp_def)

lemma pnet_node_trans [elim, simp]:
  assumes "(s, a, s') \<in> trans (pnet np \<langle>i; R\<rangle>)"
    shows "(s, a, s') \<in> node_sos (trans (np i))"
  using assms by (simp add: trans_node_comp)

lemma pnet_never_newpkt':
  assumes "(s, a, s') \<in> trans (pnet np n)"
    shows "\<forall>i d di. a \<noteq> i:newpkt(d, di)"
  using assms proof (induction n arbitrary: s a s')
    fix n1 n2 s a s'
    assume IH1: "\<And>s a s'. (s, a, s') \<in> trans (pnet np n1) \<Longrightarrow> \<forall>i d di. a \<noteq> i:newpkt(d, di)"
       and IH2: "\<And>s a s'. (s, a, s') \<in> trans (pnet np n2) \<Longrightarrow> \<forall>i d di. a \<noteq> i:newpkt(d, di)"
       and "(s, a, s') \<in> trans (pnet np (n1 \<parallel> n2))"
    show "\<forall>i d di. a \<noteq> i:newpkt(d, di)"
    proof (intro allI)
      fix i d di
      from \<open>(s, a, s') \<in> trans (pnet np (n1 \<parallel> n2))\<close>
        have "(s, a, s') \<in> pnet_sos (trans (pnet np n1)) (trans (pnet np n2))"
          by simp
      thus "a \<noteq> i:newpkt(d, di)"
        by (rule pnet_sos_never_newpkt) (auto dest!: IH1 IH2)
    qed
  qed (simp add: node_comps)

lemma pnet_never_newpkt:
  assumes "(s, a, s') \<in> trans (pnet np n)"
    shows "a \<noteq> i:newpkt(d, di)"
  proof -
    from assms have "\<forall>i d di. a \<noteq> i:newpkt(d, di)"
      by (rule pnet_never_newpkt')
    thus ?thesis by clarsimp
  qed

subsection "Table 5: Structural operational semantics for complete network expressions "

inductive_set
  cnet_sos :: "('s, ('m::msg) node_action) transition set
                    \<Rightarrow> ('s, 'm node_action) transition set"
  for S :: "('s, 'm node_action) transition set"
where
    cnet_connect: "(s, connect(i, i'), s') \<in> S  \<Longrightarrow> (s, connect(i, i'), s') \<in> cnet_sos S"
  | cnet_disconnect: "(s, disconnect(i, i'), s') \<in> S  \<Longrightarrow> (s, disconnect(i, i'), s') \<in> cnet_sos S"
  | cnet_cast: "(s, R:*cast(m), s') \<in> S  \<Longrightarrow> (s, \<tau>, s') \<in> cnet_sos S"
  | cnet_tau: "(s, \<tau>, s') \<in> S  \<Longrightarrow> (s, \<tau>, s') \<in> cnet_sos S"
  | cnet_deliver: "(s, i:deliver(d), s') \<in> S  \<Longrightarrow> (s, i:deliver(d), s') \<in> cnet_sos S"
  | cnet_newpkt: "(s, {i}\<not>K:arrive(newpkt(d, di)), s') \<in> S  \<Longrightarrow> (s, i:newpkt(d, di), s') \<in> cnet_sos S"

inductive_cases connect_completeTE: "(s, connect(i, i'), s') \<in> cnet_sos S"
            and disconnect_completeTE: "(s, disconnect(i, i'), s') \<in> cnet_sos S"
            and tau_completeTE: "(s, \<tau>, s') \<in> cnet_sos S"
            and deliver_completeTE: "(s, i:deliver(d), s') \<in> cnet_sos S"
            and newpkt_completeTE: "(s, i:newpkt(d, di), s') \<in> cnet_sos S"

lemmas completeTEs = connect_completeTE
                     disconnect_completeTE
                     tau_completeTE
                     deliver_completeTE
                     newpkt_completeTE

lemma complete_no_cast [simp]:
  "(s, R:*cast(m), s') \<notin> cnet_sos T"
  proof
    assume "(s, R:*cast(m), s') \<in> cnet_sos T"
    hence "R:*cast(m) \<noteq> R:*cast(m)"
     by (rule cnet_sos.cases) auto
    thus False by simp
  qed

lemma complete_no_arrive [simp]:
  "(s, ii\<not>ni:arrive(m), s') \<notin> cnet_sos T"
  proof
    assume "(s, ii\<not>ni:arrive(m), s') \<in> cnet_sos T"
    hence "ii\<not>ni:arrive(m) \<noteq> ii\<not>ni:arrive(m)"
     by (rule cnet_sos.cases) auto
    thus False by simp
  qed

abbreviation
  closed :: "('s net_state, ('m::msg) node_action) automaton \<Rightarrow> ('s net_state, 'm node_action) automaton"
where
  "closed \<equiv> (\<lambda>A. A \<lparr> trans := cnet_sos (trans A) \<rparr>)"

end

