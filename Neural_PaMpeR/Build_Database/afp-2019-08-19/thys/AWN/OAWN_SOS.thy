(*  Title:       OAWN_SOS.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Open semantics of the Algebra of Wireless Networks"

theory OAWN_SOS
imports TransitionSystems AWN
begin

text \<open>
  These are variants of the SOS rules that work against a mixed global/local context, where
  the global context is represented by a function @{term \<sigma>} mapping ip addresses to states.
\<close>

subsection "Open structural operational semantics for sequential process expressions "

inductive_set
  oseqp_sos
  :: "('s, 'm, 'p, 'l) seqp_env \<Rightarrow> ip
      \<Rightarrow> ((ip \<Rightarrow> 's) \<times> ('s, 'm, 'p, 'l) seqp, 'm seq_action) transition set"
  for \<Gamma> :: "('s, 'm, 'p, 'l) seqp_env"
  and i :: ip
where
    obroadcastT: "\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g).p),        broadcast (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)),              (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | ogroupcastT: "\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g).p),  groupcast (s\<^sub>i\<^sub>p\<^sub>s (\<sigma> i)) (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)), (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | ounicastT:   "\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q), unicast (s\<^sub>i\<^sub>p (\<sigma> i)) (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)),    (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | onotunicastT:"\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g).p \<triangleright> q), \<not>unicast (s\<^sub>i\<^sub>p (\<sigma> i)),               (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  | osendT:      "\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}send(s\<^sub>m\<^sub>s\<^sub>g).p),             send (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)),                  (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | odeliverT:   "\<sigma>' i = \<sigma> i \<Longrightarrow>
                  ((\<sigma>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a).p),         deliver (s\<^sub>d\<^sub>a\<^sub>t\<^sub>a (\<sigma> i)),              (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | oreceiveT:   "\<sigma>' i = u\<^sub>m\<^sub>s\<^sub>g msg (\<sigma> i) \<Longrightarrow>
                  ((\<sigma>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g).p),          receive msg,                       (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"
  | oassignT:    "\<sigma>' i = u (\<sigma> i) \<Longrightarrow>
                  ((\<sigma>, {l}\<lbrakk>u\<rbrakk> p),                    \<tau>,                                 (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"

  | ocallT:      "((\<sigma>, \<Gamma> pn), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i \<Longrightarrow>
                  ((\<sigma>, call(pn)), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i" (* TPB: quite different to Table 1 *)

  | ochoiceT1:   "((\<sigma>, p), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i \<Longrightarrow>
                  ((\<sigma>, p \<oplus> q), a, (\<sigma>', p')) \<in> oseqp_sos \<Gamma> i"
  | ochoiceT2:   "((\<sigma>, q), a, (\<sigma>', q')) \<in> oseqp_sos \<Gamma> i \<Longrightarrow>
                  ((\<sigma>, p \<oplus> q), a, (\<sigma>', q')) \<in> oseqp_sos \<Gamma> i"

  | oguardT:     "\<sigma>' i \<in> g (\<sigma> i) \<Longrightarrow> ((\<sigma>, {l}\<langle>g\<rangle> p), \<tau>, (\<sigma>', p)) \<in> oseqp_sos \<Gamma> i"

inductive_cases
      oseq_callTE [elim]:      "((\<sigma>, call(pn)), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"
  and oseq_choiceTE [elim]:    "((\<sigma>, p1 \<oplus> p2), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i"

lemma oseq_broadcastTE [elim]:
  "\<lbrakk>((\<sigma>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
    \<lbrakk>a = broadcast (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)); \<sigma>' i = \<sigma> i; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}broadcast(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_groupcastTE [elim]:
  "\<lbrakk>((\<sigma>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
    \<lbrakk>a = groupcast (s\<^sub>i\<^sub>p\<^sub>s (\<sigma> i)) (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)); \<sigma>' i = \<sigma> i; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}groupcast(s\<^sub>i\<^sub>p\<^sub>s, s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_unicastTE [elim]:
  "\<lbrakk>((\<sigma>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q), a, (\<sigma>', r)) \<in> oseqp_sos \<Gamma> i;
    \<lbrakk>a = unicast (s\<^sub>i\<^sub>p (\<sigma> i)) (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)); \<sigma>' i = \<sigma> i; r = p\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>a = \<not>unicast (s\<^sub>i\<^sub>p (\<sigma> i)); \<sigma>' i = \<sigma> i; r = q\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}unicast(s\<^sub>i\<^sub>p, s\<^sub>m\<^sub>s\<^sub>g). p \<triangleright> q), a, (\<sigma>', r)) \<in> oseqp_sos \<Gamma> i") simp_all

lemma oseq_sendTE [elim]:
  "\<lbrakk>((\<sigma>, {l}send(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
    \<lbrakk>a = send (s\<^sub>m\<^sub>s\<^sub>g (\<sigma> i)); \<sigma>' i = \<sigma> i; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}send(s\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_deliverTE [elim]:
  "\<lbrakk>((\<sigma>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
    \<lbrakk>a = deliver (s\<^sub>d\<^sub>a\<^sub>t\<^sub>a (\<sigma> i)); \<sigma>' i = \<sigma> i; q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}deliver(s\<^sub>d\<^sub>a\<^sub>t\<^sub>a). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_receiveTE [elim]:
  "\<lbrakk>((\<sigma>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i;
    \<And>msg. \<lbrakk>a = receive msg; \<sigma>' i = u\<^sub>m\<^sub>s\<^sub>g msg (\<sigma> i); q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}receive(u\<^sub>m\<^sub>s\<^sub>g). p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_assignTE [elim]:
  "\<lbrakk>((\<sigma>, {l}\<lbrakk>u\<rbrakk> p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i; \<lbrakk>a = \<tau>; \<sigma>' i = u (\<sigma> i); q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}\<lbrakk>u\<rbrakk> p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemma oseq_guardTE [elim]:
  "\<lbrakk>((\<sigma>, {l}\<langle>g\<rangle> p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i; \<lbrakk>a = \<tau>; \<sigma>' i \<in> g (\<sigma> i); q = p\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, {l}\<langle>g\<rangle> p), a, (\<sigma>', q)) \<in> oseqp_sos \<Gamma> i") simp

lemmas oseqpTEs =
  oseq_broadcastTE
  oseq_groupcastTE
  oseq_unicastTE
  oseq_sendTE
  oseq_deliverTE
  oseq_receiveTE
  oseq_assignTE
  oseq_callTE
  oseq_choiceTE
  oseq_guardTE

declare oseqp_sos.intros [intro]

subsection "Open structural operational semantics for parallel process expressions "

inductive_set
  oparp_sos :: "ip
               \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 's1, 'm seq_action) transition set
               \<Rightarrow> ('s2, 'm seq_action) transition set
               \<Rightarrow> ((ip \<Rightarrow> 's) \<times> ('s1 \<times> 's2), 'm seq_action) transition set"
  for i :: ip
  and S :: "((ip \<Rightarrow> 's) \<times> 's1, 'm seq_action) transition set"
  and T :: "('s2, 'm seq_action) transition set"
where
    oparleft:  "\<lbrakk> ((\<sigma>, s), a, (\<sigma>', s')) \<in> S; \<And>m. a \<noteq> receive m \<rbrakk> \<Longrightarrow>
                ((\<sigma>, (s, t)), a, (\<sigma>', (s', t))) \<in> oparp_sos i S T"
  | oparright: "\<lbrakk> (t, a, t') \<in> T; \<And>m. a \<noteq> send m; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow>
                ((\<sigma>, (s, t)), a, (\<sigma>', (s, t'))) \<in> oparp_sos i S T"
  | oparboth:  "\<lbrakk> ((\<sigma>, s), receive m, (\<sigma>', s')) \<in> S; (t, send m, t') \<in> T \<rbrakk> \<Longrightarrow>
                ((\<sigma>, (s, t)), \<tau>, (\<sigma>', (s', t'))) \<in> oparp_sos i S T"

lemma opar_broadcastTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), broadcast m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), broadcast m, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, broadcast m, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), broadcast m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") simp_all

lemma opar_groupcastTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), groupcast ips m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), groupcast ips m, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, groupcast ips m, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), groupcast ips m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") simp_all

lemma opar_unicastTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), unicast i m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), unicast i m, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, unicast i m, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), unicast i m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") simp_all

lemma opar_notunicastTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), notunicast i, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), notunicast i, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, notunicast i, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), notunicast i, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") simp_all

lemma opar_sendTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), send m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), send m, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), send m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") auto

lemma opar_deliverTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), deliver d, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>((\<sigma>, s), deliver d, (\<sigma>', s')) \<in> S; t' = t\<rbrakk> \<Longrightarrow> P;
    \<lbrakk>(t, deliver d, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), deliver d, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") simp_all

lemma opar_receiveTE [elim]:
  "\<lbrakk>((\<sigma>, (s, t)), receive m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T;
    \<lbrakk>(t, receive m, t') \<in> T; s' = s; \<sigma>' i = \<sigma> i\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (ind_cases "((\<sigma>, (s, t)), receive m, (\<sigma>', (s', t'))) \<in> oparp_sos i S T") auto

inductive_cases opar_tauTE: "((\<sigma>, (s, t)), \<tau>, (\<sigma>', (s', t'))) \<in> oparp_sos i S T"

lemmas oparpTEs =
  opar_broadcastTE
  opar_groupcastTE
  opar_unicastTE
  opar_notunicastTE
  opar_sendTE
  opar_deliverTE
  opar_receiveTE

lemma oparp_sos_cases [elim]:
  assumes "((\<sigma>, (s, t)), a, (\<sigma>', (s', t'))) \<in> oparp_sos i S T"
      and "\<lbrakk> ((\<sigma>, s), a, (\<sigma>', s')) \<in> S; \<And>m. a \<noteq> receive m; t' = t \<rbrakk> \<Longrightarrow> P"
      and "\<lbrakk> (t, a, t') \<in> T; \<And>m. a \<noteq> send m; s' = s; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P"
      and "\<And>m. \<lbrakk> a = \<tau>; ((\<sigma>, s), receive m, (\<sigma>', s')) \<in> S; (t, send m, t') \<in> T \<rbrakk> \<Longrightarrow> P"
    shows "P"
  using assms by cases auto

definition extg :: "('a \<times> 'b) \<times> 'c \<Rightarrow> 'a \<times> 'b \<times> 'c"
where "extg \<equiv> \<lambda>((\<sigma>, l1), l2). (\<sigma>, (l1, l2))"

lemma extgsimp [simp]:
  "extg ((\<sigma>, l1), l2) = (\<sigma>, (l1, l2))"
  unfolding extg_def by simp

lemma extg_range_prod: "extg ` (i1 \<times> i2) = {(\<sigma>, (s1, s2))|\<sigma> s1 s2. (\<sigma>, s1) \<in> i1 \<and> s2 \<in> i2}"
  unfolding image_def extg_def
  by (rule Collect_cong) (auto split: prod.split)

definition
  opar_comp :: "((ip \<Rightarrow> 's) \<times> 's1, 'm seq_action) automaton
               \<Rightarrow> ip
               \<Rightarrow> ('s2, 'm seq_action) automaton
               \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 's1 \<times> 's2, 'm seq_action) automaton"
  ("(_ \<langle>\<langle>\<^bsub>_\<^esub> _)" [102, 0, 103] 102)
where
  "s \<langle>\<langle>\<^bsub>i\<^esub> t \<equiv> \<lparr> init = extg ` (init s \<times> init t), trans = oparp_sos i (trans s) (trans t) \<rparr>"

lemma opar_comp_def':
  "s \<langle>\<langle>\<^bsub>i\<^esub> t = \<lparr> init = {(\<sigma>, (s\<^sub>l, t\<^sub>l))|\<sigma> s\<^sub>l t\<^sub>l. (\<sigma>, s\<^sub>l) \<in> init s \<and> t\<^sub>l \<in> init t},
                trans = oparp_sos i (trans s) (trans t) \<rparr>"
  unfolding opar_comp_def extg_def image_def by (auto split: prod.split)

lemma trans_opar_comp [simp]:
  "trans (s \<langle>\<langle>\<^bsub>i\<^esub> t) = oparp_sos i (trans s) (trans t)"
  unfolding opar_comp_def by simp

lemma init_opar_comp [simp]:
  "init (s \<langle>\<langle>\<^bsub>i\<^esub> t) = extg ` (init s \<times> init t)"
  unfolding opar_comp_def by simp

subsection "Open structural operational semantics for node expressions "

inductive_set
  onode_sos :: "((ip \<Rightarrow> 's) \<times> 'l, 'm seq_action) transition set
                \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
  for S :: "((ip \<Rightarrow> 's) \<times> 'l, 'm seq_action) transition set"
where
    onode_bcast:
    "((\<sigma>, s), broadcast m, (\<sigma>', s')) \<in> S \<Longrightarrow> ((\<sigma>, NodeS i s R), R:*cast(m), (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_gcast:
    "((\<sigma>, s), groupcast D m, (\<sigma>', s')) \<in> S \<Longrightarrow> ((\<sigma>, NodeS i s R), (R\<inter>D):*cast(m), (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_ucast:
    "\<lbrakk> ((\<sigma>, s), unicast d m, (\<sigma>', s')) \<in> S; d\<in>R \<rbrakk> \<Longrightarrow> ((\<sigma>, NodeS i s R), {d}:*cast(m), (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

    (* Such assumptions aid later proofs, but they must be justified when transferring results
       to closed systems. *)
  | onode_notucast: "\<lbrakk> ((\<sigma>, s), \<not>unicast d, (\<sigma>', s')) \<in> S; d\<notin>R; \<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j \<rbrakk>
     \<Longrightarrow> ((\<sigma>, NodeS i s R), \<tau>, (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_deliver: "\<lbrakk> ((\<sigma>, s), deliver d, (\<sigma>', s')) \<in> S; \<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j \<rbrakk>
     \<Longrightarrow> ((\<sigma>, NodeS i s R), i:deliver(d), (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_tau: "\<lbrakk> ((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> S; \<forall>j. j\<noteq>i \<longrightarrow> \<sigma>' j = \<sigma> j \<rbrakk>
     \<Longrightarrow> ((\<sigma>, NodeS i s R),   \<tau>, (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_receive:
    "((\<sigma>, s), receive m, (\<sigma>', s')) \<in> S \<Longrightarrow> ((\<sigma>, NodeS i s R), {i}\<not>{}:arrive(m), (\<sigma>', NodeS i s' R)) \<in> onode_sos S"

  | onode_arrive:
    "\<sigma>' i = \<sigma> i \<Longrightarrow> ((\<sigma>, NodeS i s R), {}\<not>{i}:arrive(m),  (\<sigma>', NodeS i s R)) \<in> onode_sos S"

  | onode_connect1:
    "\<sigma>' i = \<sigma> i \<Longrightarrow> ((\<sigma>, NodeS i s R), connect(i, i'),    (\<sigma>', NodeS i s (R \<union> {i'}))) \<in> onode_sos S"

  | onode_connect2:
    "\<sigma>' i = \<sigma> i \<Longrightarrow> ((\<sigma>, NodeS i s R), connect(i', i),    (\<sigma>', NodeS i s (R \<union> {i'}))) \<in> onode_sos S"

  | onode_disconnect1:
    "\<sigma>' i = \<sigma> i \<Longrightarrow> ((\<sigma>, NodeS i s R), disconnect(i, i'), (\<sigma>', NodeS i s (R - {i'}))) \<in> onode_sos S"

  | onode_disconnect2:
    "\<sigma>' i = \<sigma> i \<Longrightarrow> ((\<sigma>, NodeS i s R), disconnect(i', i), (\<sigma>', NodeS i s (R - {i'}))) \<in> onode_sos S"

  | onode_connect_other:
    "\<lbrakk> i \<noteq> i'; i \<noteq> i''; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> ((\<sigma>, NodeS i s R), connect(i', i''),    (\<sigma>', NodeS i s R)) \<in> onode_sos S"

  | onode_disconnect_other:
    "\<lbrakk> i \<noteq> i'; i \<noteq> i''; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> ((\<sigma>, NodeS i s R), disconnect(i', i''), (\<sigma>', NodeS i s R)) \<in> onode_sos S"

inductive_cases
      onode_arriveTE [elim]:     "((\<sigma>, NodeS i s R), ii\<not>ni:arrive(m),   (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_castTE [elim]:       "((\<sigma>, NodeS i s R), RR:*cast(m),        (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_deliverTE [elim]:    "((\<sigma>, NodeS i s R), ii:deliver(d),      (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_connectTE [elim]:    "((\<sigma>, NodeS i s R), connect(ii, ii'),   (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_disconnectTE [elim]: "((\<sigma>, NodeS i s R), disconnect(ii, ii'),(\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_newpktTE [elim]:     "((\<sigma>, NodeS i s R), ii:newpkt(d, di),   (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
  and onode_tauTE [elim]:        "((\<sigma>, NodeS i s R), \<tau>,                  (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"

lemma oarrives_or_not:
  assumes "((\<sigma>, NodeS i s R), ii\<not>ni:arrive(m), (\<sigma>', NodeS i' s' R')) \<in> onode_sos S"
    shows "(ii = {i} \<and> ni = {}) \<or> (ii = {} \<and> ni = {i})"
  using assms by rule simp_all

definition
  onode_comp :: "ip
                 \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l, 'm seq_action) automaton
                 \<Rightarrow> ip set
                 \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) automaton"
    ("(\<langle>_ : (_) : _\<rangle>\<^sub>o)" [0, 0, 0] 104)
where
  "\<langle>i : onp : R\<^sub>i\<rangle>\<^sub>o \<equiv> \<lparr> init = {(\<sigma>, NodeS i s R\<^sub>i)|\<sigma> s. (\<sigma>, s) \<in> init onp},
                      trans = onode_sos (trans onp) \<rparr>"

lemma trans_onode_comp:
  "trans (\<langle>i : S : R\<rangle>\<^sub>o) = onode_sos (trans S)"
  unfolding onode_comp_def by simp

lemma init_onode_comp:
  "init (\<langle>i : S : R\<rangle>\<^sub>o) = {(\<sigma>, NodeS i s R)|\<sigma> s. (\<sigma>, s) \<in> init S}"
  unfolding onode_comp_def by simp

lemmas onode_comps = trans_onode_comp init_onode_comp

lemma fst_par_onode_comp [simp]:
  "trans (\<langle>i : s \<langle>\<langle>\<^bsub>I\<^esub> t : R\<rangle>\<^sub>o) = onode_sos (oparp_sos I (trans s) (trans t))"
  unfolding onode_comp_def by simp

lemma init_par_onode_comp [simp]:
  "init (\<langle>i : s \<langle>\<langle>\<^bsub>I\<^esub> t : R\<rangle>\<^sub>o) = {(\<sigma>, NodeS i (s1, s2) R)|\<sigma> s1 s2. ((\<sigma>, s1), s2) \<in> init s \<times> init t}"
  unfolding onode_comp_def by (simp add: extg_range_prod)

lemma onode_sos_dest_is_net_state:
  assumes "((\<sigma>, p), a, s') \<in> onode_sos S"
    shows "\<exists>\<sigma>' i' \<zeta>' R'. s' = (\<sigma>', NodeS i' \<zeta>' R')"
  using assms proof -
    assume "((\<sigma>, p), a, s') \<in> onode_sos S"
    then obtain \<sigma>' i' \<zeta>' R' where "s' = (\<sigma>', NodeS i' \<zeta>' R')"
      by (cases s') (auto elim!: onode_sos.cases)
    thus ?thesis by simp
  qed

lemma onode_sos_dest_is_net_state':
  assumes "((\<sigma>, NodeS i p R), a, s') \<in> onode_sos S"
    shows "\<exists>\<sigma>' \<zeta>' R'. s' = (\<sigma>', NodeS i \<zeta>' R')"
  using assms proof -
    assume "((\<sigma>, NodeS i p R), a, s') \<in> onode_sos S"
    then obtain \<sigma>' \<zeta>' R' where "s' = (\<sigma>', NodeS i \<zeta>' R')"
      by (cases s') (auto elim!: onode_sos.cases)
    thus ?thesis by simp
  qed

lemma onode_sos_dest_is_net_state'':
  assumes "((\<sigma>, NodeS i p R), a, (\<sigma>', s')) \<in> onode_sos S"
    shows "\<exists>\<zeta>' R'. s' = NodeS i \<zeta>' R'"
  proof -
    define ns' where "ns' = (\<sigma>', s')"
    with assms have "((\<sigma>, NodeS i p R), a, ns') \<in> onode_sos S" by simp
    then obtain \<sigma>'' \<zeta>' R' where "ns' = (\<sigma>'', NodeS i \<zeta>' R')"
      by (metis onode_sos_dest_is_net_state')
    hence "s' = NodeS i \<zeta>' R'" by (simp add: ns'_def)
    thus ?thesis by simp
  qed

lemma onode_sos_src_is_net_state:
  assumes "((\<sigma>, p), a, s') \<in> onode_sos S"
    shows "\<exists>i \<zeta> R. p = NodeS i \<zeta> R"
  using assms proof -
    assume "((\<sigma>, p), a, s') \<in> onode_sos S"
    then obtain i \<zeta> R where "p = NodeS i \<zeta> R"
      by (cases s') (auto elim!: onode_sos.cases)
    thus ?thesis by simp
  qed

lemma onode_sos_net_states:
  assumes "((\<sigma>, s), a, (\<sigma>', s')) \<in> onode_sos S"
    shows "\<exists>i \<zeta> R \<zeta>' R'. s = NodeS i \<zeta> R \<and> s' = NodeS i \<zeta>' R'"
  proof -
    from assms obtain i \<zeta> R where "s = NodeS i \<zeta> R"
      by (metis onode_sos_src_is_net_state)
    moreover with assms obtain \<zeta>' R' where "s' = NodeS i \<zeta>' R'"
      by (auto dest!: onode_sos_dest_is_net_state')
    ultimately show ?thesis by simp
  qed

lemma node_sos_cases [elim]:
  "((\<sigma>, NodeS i p R), a, (\<sigma>', NodeS i p' R')) \<in> onode_sos S \<Longrightarrow>
  (\<And>m .       \<lbrakk> a = R:*cast(m);          R' = R; ((\<sigma>, p), broadcast m,   (\<sigma>', p')) \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m D.      \<lbrakk> a = (R \<inter> D):*cast(m);    R' = R; ((\<sigma>, p), groupcast D m, (\<sigma>', p')) \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d m.      \<lbrakk> a = {d}:*cast(m);        R' = R; ((\<sigma>, p), unicast d m,   (\<sigma>', p')) \<in> S; d \<in> R \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d.        \<lbrakk> a = \<tau>;                   R' = R; ((\<sigma>, p), \<not>unicast d,    (\<sigma>', p')) \<in> S; d \<notin> R \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>d.        \<lbrakk> a = i:deliver(d);        R' = R; ((\<sigma>, p), deliver d,     (\<sigma>', p')) \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m.        \<lbrakk> a = {i}\<not>{}:arrive(m);    R' = R; ((\<sigma>, p), receive m,     (\<sigma>', p')) \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (            \<lbrakk> a = \<tau>;                   R' = R; ((\<sigma>, p), \<tau>,             (\<sigma>', p')) \<in> S \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>m.        \<lbrakk> a = {}\<not>{i}:arrive(m);    R' = R; p = p'; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = connect(i, i');      R' = R \<union> {i'}; p = p'; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = connect(i', i);      R' = R \<union> {i'}; p = p'; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = disconnect(i, i');   R' = R - {i'}; p = p'; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i'.     \<lbrakk> a = disconnect(i', i);   R' = R - {i'}; p = p'; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i' i''. \<lbrakk> a = connect(i', i'');    R' = R; p = p'; i \<noteq> i'; i \<noteq> i''; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  (\<And>i i' i''. \<lbrakk> a = disconnect(i', i''); R' = R; p = p'; i \<noteq> i'; i \<noteq> i''; \<sigma>' i = \<sigma> i \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
  P"
  by (erule onode_sos.cases) (simp | metis)+

subsection "Open structural operational semantics for partial network expressions "

inductive_set
  opnet_sos :: "((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set
                       \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set
                       \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
  for S :: "((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
  and T :: "((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
where
    opnet_cast1:
    "\<lbrakk> ((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> S; ((\<sigma>, t), H\<not>K:arrive(m), (\<sigma>', t')) \<in> T; H \<subseteq> R; K \<inter> R = {} \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t), R:*cast(m), (\<sigma>', SubnetS s' t')) \<in> opnet_sos S T"

  | opnet_cast2:
    "\<lbrakk> ((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> S; ((\<sigma>, t), R:*cast(m), (\<sigma>', t')) \<in> T;  H \<subseteq> R; K \<inter> R = {} \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t), R:*cast(m), (\<sigma>', SubnetS s' t')) \<in> opnet_sos S T"

  | opnet_arrive:
    "\<lbrakk> ((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> S; ((\<sigma>, t), H'\<not>K':arrive(m), (\<sigma>', t')) \<in> T \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t),  (H \<union> H')\<not>(K \<union> K'):arrive(m), (\<sigma>', SubnetS s' t')) \<in> opnet_sos S T"

  | opnet_deliver1:
    "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> S
      \<Longrightarrow> ((\<sigma>, SubnetS s t), i:deliver(d), (\<sigma>', SubnetS s' t)) \<in> opnet_sos S T"

  | opnet_deliver2:
    "\<lbrakk> ((\<sigma>, t), i:deliver(d), (\<sigma>', t')) \<in> T \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t), i:deliver(d), (\<sigma>', SubnetS s t')) \<in> opnet_sos S T"

  | opnet_tau1:
    "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> S \<Longrightarrow> ((\<sigma>, SubnetS s t), \<tau>, (\<sigma>', SubnetS s' t)) \<in> opnet_sos S T"

  | opnet_tau2:
    "((\<sigma>, t), \<tau>, (\<sigma>', t')) \<in> T \<Longrightarrow> ((\<sigma>, SubnetS s t), \<tau>, (\<sigma>', SubnetS s t')) \<in> opnet_sos S T"

  | opnet_connect:
    "\<lbrakk> ((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> S; ((\<sigma>, t), connect(i, i'), (\<sigma>', t')) \<in> T \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t), connect(i, i'), (\<sigma>', SubnetS s' t')) \<in> opnet_sos S T"

  | opnet_disconnect:
    "\<lbrakk> ((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> S; ((\<sigma>, t), disconnect(i, i'), (\<sigma>', t')) \<in> T \<rbrakk>
      \<Longrightarrow> ((\<sigma>, SubnetS s t), disconnect(i, i'), (\<sigma>', SubnetS s' t')) \<in> opnet_sos S T"

inductive_cases opartial_castTE [elim]:       "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_arriveTE [elim]:     "((\<sigma>, s), H\<not>K:arrive(m), (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_deliverTE [elim]:    "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_tauTE [elim]:        "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_connectTE [elim]:    "((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_disconnectTE [elim]: "((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> opnet_sos S T"
            and opartial_newpktTE [elim]:     "((\<sigma>, s), i:newpkt(d, di), (\<sigma>', s')) \<in> opnet_sos S T"

fun opnet :: "(ip \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l, 'm seq_action) automaton)
              \<Rightarrow> net_tree \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) automaton"
where
    "opnet onp (\<langle>i; R\<^sub>i\<rangle>)  =  \<langle>i : onp i : R\<^sub>i\<rangle>\<^sub>o"
  | "opnet onp (p\<^sub>1 \<parallel> p\<^sub>2) = \<lparr> init = {(\<sigma>, SubnetS s\<^sub>1 s\<^sub>2) |\<sigma> s\<^sub>1 s\<^sub>2.
                                        (\<sigma>, s\<^sub>1) \<in> init (opnet onp p\<^sub>1)
                                      \<and> (\<sigma>, s\<^sub>2) \<in> init (opnet onp p\<^sub>2)
                                      \<and> net_ips s\<^sub>1 \<inter> net_ips s\<^sub>2 = {}},
                             trans = opnet_sos (trans (opnet onp p\<^sub>1)) (trans (opnet onp p\<^sub>2)) \<rparr>"

lemma opnet_node_init [elim, simp]:
  assumes "(\<sigma>, s) \<in> init (opnet onp \<langle>i; R\<rangle>)"
    shows "(\<sigma>, s) \<in> { (\<sigma>, NodeS i ns R) |\<sigma> ns. (\<sigma>, ns) \<in> init (onp i)}"
  using assms by (simp add: onode_comp_def)

lemma opnet_node_init' [elim]:
 assumes "(\<sigma>, s) \<in> init (opnet onp \<langle>i; R\<rangle>)"
 obtains ns where "s = NodeS i ns R"
             and "(\<sigma>, ns) \<in> init (onp i)"
   using assms by (auto simp add: onode_comp_def)

lemma opnet_node_trans [elim, simp]:
  assumes "(s, a, s') \<in> trans (opnet onp \<langle>i; R\<rangle>)"
    shows "(s, a, s') \<in> onode_sos (trans (onp i))"
  using assms by (simp add: trans_onode_comp)

subsection "Open structural operational semantics for complete network expressions "

inductive_set
  ocnet_sos :: "((ip \<Rightarrow> 's) \<times> 'l net_state, 'm::msg node_action) transition set
                         \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
  for S :: "((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) transition set"
where
    ocnet_connect:
    "\<lbrakk> ((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> ocnet_sos S"

  | ocnet_disconnect:
    "\<lbrakk> ((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> ocnet_sos S"

  | ocnet_cast:
    "\<lbrakk> ((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> ocnet_sos S"

  | ocnet_tau:  
    "\<lbrakk> ((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> ocnet_sos S"

  | ocnet_deliver:
    "\<lbrakk> ((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> ocnet_sos S"

  | ocnet_newpkt:
    "\<lbrakk> ((\<sigma>, s), {i}\<not>K:arrive(newpkt(d, di)), (\<sigma>', s')) \<in> S; \<forall>j. j \<notin> net_ips s \<longrightarrow> (\<sigma>' j = \<sigma> j) \<rbrakk>
     \<Longrightarrow> ((\<sigma>, s), i:newpkt(d, di), (\<sigma>', s')) \<in> ocnet_sos S"

inductive_cases oconnect_completeTE: "((\<sigma>, s), connect(i, i'), (\<sigma>', s')) \<in> ocnet_sos S"
            and odisconnect_completeTE: "((\<sigma>, s), disconnect(i, i'), (\<sigma>', s')) \<in> ocnet_sos S"
            and otau_completeTE: "((\<sigma>, s), \<tau>, (\<sigma>', s')) \<in> ocnet_sos S"
            and odeliver_completeTE: "((\<sigma>, s), i:deliver(d), (\<sigma>', s')) \<in> ocnet_sos S"
            and onewpkt_completeTE: "((\<sigma>, s), i:newpkt(d, di), (\<sigma>', s')) \<in> ocnet_sos S"

lemmas ocompleteTEs = oconnect_completeTE
                      odisconnect_completeTE
                      otau_completeTE
                      odeliver_completeTE
                      onewpkt_completeTE

lemma ocomplete_no_cast [simp]:
  "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<notin> ocnet_sos T"
  proof
    assume "((\<sigma>, s), R:*cast(m), (\<sigma>', s')) \<in> ocnet_sos T"
    hence "R:*cast(m) \<noteq> R:*cast(m)"
     by (rule ocnet_sos.cases) auto
    thus False by simp
  qed

lemma ocomplete_no_arrive [simp]:
  "((\<sigma>, s), ii\<not>ni:arrive(m), (\<sigma>', s')) \<notin> ocnet_sos T"
  proof
    assume "((\<sigma>, s), ii\<not>ni:arrive(m), (\<sigma>', s')) \<in> ocnet_sos T"
    hence "ii\<not>ni:arrive(m) \<noteq> ii\<not>ni:arrive(m)"
     by (rule ocnet_sos.cases) auto
    thus False by simp
  qed

lemma ocomplete_no_change [elim]:
  assumes "((\<sigma>, s), a, (\<sigma>', s')) \<in> ocnet_sos T"
      and "j \<notin> net_ips s"
    shows "\<sigma>' j = \<sigma> j"
  using assms by cases simp_all

lemma ocomplete_transE [elim]:
  assumes "((\<sigma>, \<zeta>), a, (\<sigma>', \<zeta>')) \<in> ocnet_sos (trans (opnet onp n))"
  obtains a' where "((\<sigma>, \<zeta>), a', (\<sigma>', \<zeta>')) \<in> trans (opnet onp n)"
  using assms by (cases a) (auto elim!: ocompleteTEs [simplified])

abbreviation
  oclosed :: "((ip \<Rightarrow> 's) \<times> 'l net_state, ('m::msg) node_action) automaton
              \<Rightarrow> ((ip \<Rightarrow> 's) \<times> 'l net_state, 'm node_action) automaton"
where
  "oclosed \<equiv> (\<lambda>A. A \<lparr> trans := ocnet_sos (trans A) \<rparr>)"

end

