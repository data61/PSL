(*  Title:       Toy.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
    Author:      Peter Höfner
*)

section "Simple toy example"

theory Toy
imports Main AWN_Main Qmsg_Lifting
begin

subsection "Messages used in the protocol"

datatype msg =
    Pkt data ip
  | Newpkt data ip

instantiation msg :: msg
begin
definition newpkt_def [simp]: "newpkt \<equiv> \<lambda>(d,did). Newpkt d did"
definition eq_newpkt_def: "eq_newpkt m \<equiv> case m of Newpkt d did  \<Rightarrow> True | _ \<Rightarrow> False" 

instance by intro_classes (simp add: eq_newpkt_def)
end

definition pkt :: "nat \<times> nat \<Rightarrow> msg"
where "pkt \<equiv> \<lambda>(no, sid). Pkt no sid"

lemma pkt_simp [simp]:
  "pkt(no, sid) = Pkt no sid"
  unfolding pkt_def by simp

lemma not_eq_newpkt_pkt [simp]: "\<not>eq_newpkt (Pkt no sid)"
  unfolding eq_newpkt_def by simp

subsection "Protocol model"

record state =
  id    :: "nat"
  no    :: "nat"
  nhid  :: "nat"
  (* all locals *)
  msg    :: "msg"
  num    :: "nat"
  sid    :: "nat"

abbreviation toy_init :: "ip \<Rightarrow> state"
where "toy_init i \<equiv> \<lparr>
         id = i,
         no = 0,
         nhid = i,

         msg    = (SOME x. True),
         num    = (SOME x. True),
         sid    = (SOME x. True)
       \<rparr>"

lemma some_neq_not_eq [simp]: "\<not>((SOME x :: nat. x \<noteq> i) = i)"
  by (subst some_eq_ex) (metis zero_neq_numeral)

definition clear_locals :: "state \<Rightarrow> state"
where "clear_locals \<xi> = \<xi> \<lparr>
    msg    := (SOME x. True),
    num    := (SOME x. True),
    sid    := (SOME x. True)
  \<rparr>"

lemma clear_locals_but_not_globals [simp]:
  "id (clear_locals \<xi>) = id \<xi>"
  "no (clear_locals \<xi>) = no \<xi>"
  "nhid (clear_locals \<xi>) = nhid \<xi>"
  unfolding clear_locals_def by auto

definition is_newpkt
where "is_newpkt \<xi> \<equiv> case msg \<xi> of
                       Newpkt data did \<Rightarrow> { \<xi>\<lparr>num := data\<rparr> }
                     | _ \<Rightarrow> {}"

definition is_pkt
where "is_pkt \<xi> \<equiv> case msg \<xi> of
                    Pkt num' sid' \<Rightarrow> { \<xi>\<lparr> num := num', sid := sid' \<rparr> }
                  | _ \<Rightarrow> {}"

lemmas is_msg_defs =
  is_pkt_def is_newpkt_def

lemma is_msg_inv_id [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> id \<xi>' = id \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> id \<xi>' = id \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_sid [simp]:
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> sid \<xi>' = sid \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_no [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> no \<xi>' = no \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> no \<xi>' = no \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_nhid [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> nhid \<xi>' = nhid \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> nhid \<xi>' = nhid \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_msg [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> msg \<xi>' = msg \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> msg \<xi>' = msg \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

datatype pseqp =
    PToy

fun nat_of_seqp :: "pseqp \<Rightarrow> nat"
where
  "nat_of_seqp PToy = 1"

instantiation "pseqp" :: ord
begin
definition less_eq_seqp [iff]: "l1 \<le> l2 = (nat_of_seqp l1 \<le> nat_of_seqp l2)"
definition less_seqp [iff]:    "l1 < l2 = (nat_of_seqp l1 < nat_of_seqp l2)"
instance ..
end

abbreviation Toy
where
  "Toy \<equiv> \<lambda>_. \<lbrakk>clear_locals\<rbrakk> call(PToy)"

fun \<Gamma>\<^sub>T\<^sub>O\<^sub>Y :: "(state, msg, pseqp, pseqp label) seqp_env"
where
  "\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy = labelled PToy (
     receive(\<lambda>msg' \<xi>. \<xi> \<lparr> msg := msg' \<rparr>).
     \<lbrakk>\<xi>. \<xi> \<lparr>nhid := id \<xi>\<rparr>\<rbrakk>
     (   \<langle>is_newpkt\<rangle> 
         (
             \<lbrakk>\<xi>. \<xi> \<lparr>no := max (no \<xi>) (num \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. pkt(no \<xi>, id \<xi>)). Toy()
         )
       \<oplus> \<langle>is_pkt\<rangle>
       (
            \<langle>\<xi>. num \<xi> > no \<xi>\<rangle>
               \<lbrakk>\<xi>. \<xi> \<lparr>no := num \<xi>\<rparr>\<rbrakk>
               \<lbrakk>\<xi>. \<xi> \<lparr>nhid := sid \<xi>\<rparr>\<rbrakk>
               broadcast(\<lambda>\<xi>. pkt(no \<xi>, id \<xi>)). Toy()
         \<oplus> \<langle>\<xi>. num \<xi> \<le> no \<xi>\<rangle>
               Toy()
       )
     ))"

declare \<Gamma>\<^sub>T\<^sub>O\<^sub>Y.simps [simp del, code del]
lemmas \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps [simp, code] = \<Gamma>\<^sub>T\<^sub>O\<^sub>Y.simps [simplified]

fun \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton
where "\<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton PToy = seqp_skeleton (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)"

lemma \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton_wf [simp]:
  "wellformed \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton pn)"
      by (cases pn) simp_all
  qed

declare \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton.simps [simp del, code del]
lemmas \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton_simps [simp, code] = \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_skeleton.simps [simplified \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps seqp_skeleton.simps]

lemma toy_proc_cases [dest]:
  fixes p pn
  assumes "p \<in> ctermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
    shows "p \<in> ctermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)"
  using assms
  by (cases pn) simp_all

definition \<sigma>\<^sub>T\<^sub>O\<^sub>Y :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp) set"
where "\<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<equiv> {(toy_init i, \<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)}"

abbreviation ptoy
  :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "ptoy i \<equiv> \<lparr> init = \<sigma>\<^sub>T\<^sub>O\<^sub>Y i, trans = seqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y \<rparr>"

lemma toy_trans: "trans (ptoy i) = seqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  by simp

lemma toy_control_within [simp]: "control_within \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (init (ptoy i))"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps)

lemma toy_wf [simp]:
  "wellformed \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
      by (cases pn) simp_all
  qed

lemmas toy_labels_not_empty [simp] = labels_not_empty [OF toy_wf]

lemma toy_ex_label [intro]: "\<exists>l. l\<in>labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
  by (metis toy_labels_not_empty all_not_in_conv)

lemma toy_ex_labelE [elim]:
  assumes "\<forall>l\<in>labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p. P l p"
      and "\<exists>p l. P l p \<Longrightarrow> Q"
    shows "Q"
 using assms by (metis toy_ex_label) 

lemma toy_simple_labels [simp]: "simple_labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y"
  proof
    fix pn p
    assume "p\<in>subterms(\<Gamma>\<^sub>T\<^sub>O\<^sub>Y pn)"
    thus "\<exists>!l. labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {l}"
    by (cases pn) (simp_all cong: seqp_congs | elim disjE)+
  qed

lemma \<sigma>\<^sub>T\<^sub>O\<^sub>Y_labels [simp]: "(\<xi>, p) \<in> \<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<Longrightarrow>  labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {PToy-:0}"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp

text \<open>By default, we no longer let the simplifier descend into process terms.\<close>

declare seqp_congs [cong]

(* configure the inv_cterms tactic *)
declare
  \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps [cterms_env]
  toy_proc_cases [ctermsl_cases]
  seq_invariant_ctermsI [OF toy_wf toy_control_within toy_simple_labels toy_trans, cterms_intros]
  seq_step_invariant_ctermsI [OF toy_wf toy_control_within toy_simple_labels toy_trans, cterms_intros]

subsection "Define an open version of the protocol"

definition \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y :: "((ip \<Rightarrow> state) \<times> ((state, msg, pseqp, pseqp label) seqp)) set"
where "\<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y \<equiv> {(toy_init, \<Gamma>\<^sub>T\<^sub>O\<^sub>Y PToy)}"

abbreviation optoy
  :: "ip \<Rightarrow> ((ip \<Rightarrow> state) \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "optoy i \<equiv> \<lparr> init = \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y, trans = oseqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y i \<rparr>"

lemma initiali_toy [intro!, simp]: "initiali i (init (optoy i)) (init (ptoy i))"
  unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by rule simp_all

lemma oaodv_control_within [simp]: "control_within \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (init (optoy i))"
  unfolding \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>T\<^sub>O\<^sub>Y_simps)

lemma \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_labels [simp]: "(\<sigma>, p) \<in> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y \<Longrightarrow>  labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p = {PToy-:0}"
  unfolding \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def by simp

lemma otoy_trans: "trans (optoy i) = oseqp_sos \<Gamma>\<^sub>T\<^sub>O\<^sub>Y i"
  by simp

(* configure the inv_cterms tactic *)
declare
  oseq_invariant_ctermsI [OF toy_wf oaodv_control_within toy_simple_labels otoy_trans, cterms_intros]
  oseq_step_invariant_ctermsI [OF toy_wf oaodv_control_within toy_simple_labels otoy_trans, cterms_intros]

subsection "Predicates"

definition msg_sender :: "msg \<Rightarrow> ip"
where "msg_sender m \<equiv> case m of Pkt _ ipc \<Rightarrow> ipc"

lemma msg_sender_simps [simp]:
  "\<And>d did sid. msg_sender (Pkt d sid) = sid"
  unfolding msg_sender_def by simp_all

abbreviation not_Pkt :: "msg \<Rightarrow> bool"
where "not_Pkt m \<equiv> case m of Pkt _ _ \<Rightarrow> False | _ \<Rightarrow> True"

definition nos_inc :: "state \<Rightarrow> state \<Rightarrow> bool"
where "nos_inc \<xi> \<xi>' \<equiv> (no \<xi> \<le> no \<xi>')"

definition msg_ok :: "(ip \<Rightarrow> state) \<Rightarrow> msg \<Rightarrow> bool"
where "msg_ok \<sigma> m \<equiv> case m of Pkt num' sid' \<Rightarrow> num' \<le> no (\<sigma> sid') | _ \<Rightarrow> True"

lemma msg_okI [intro]:
  assumes "\<And>num' sid'. m = Pkt num' sid' \<Longrightarrow> num' \<le> no (\<sigma> sid')"
    shows "msg_ok \<sigma> m"
  using assms unfolding msg_ok_def
  by (auto split: msg.split)

lemma msg_ok_Pkt [simp]:
  "msg_ok \<sigma> (Pkt data src) = (data \<le> no (\<sigma> src))"
  unfolding msg_ok_def by simp

lemma msg_ok_pkt [simp]:
  "msg_ok \<sigma> (pkt(data, src)) = (data \<le> no (\<sigma> src))"
  unfolding msg_ok_def by simp

lemma msg_ok_Newpkt [simp]:
  "msg_ok \<sigma> (Newpkt data dst)"
  unfolding msg_ok_def by simp

lemma msg_ok_newpkt [simp]:
  "msg_ok \<sigma> (newpkt(data, dst))"
  unfolding msg_ok_def by simp

subsection "Sequential Invariants"

lemma seq_no_leq_num:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:7..PToy-:8} \<longrightarrow> no \<xi> \<le> num \<xi>)"
  by inv_cterms

lemma seq_nos_incs:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), _, (\<xi>', _)). nos_inc \<xi> \<xi>')"
  unfolding nos_inc_def
  by (inv_cterms inv add: onl_invariant_sterms [OF toy_wf seq_no_leq_num])

lemma seq_nos_incs':
  "ptoy i \<TTurnstile>\<^sub>A (\<lambda>((\<xi>, _), _, (\<xi>', _)). nos_inc \<xi> \<xi>')"
  by (rule step_invariant_weakenE [OF seq_nos_incs]) (auto dest!: onllD)

lemma sender_ip_valid:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), a, _). anycast (\<lambda>m. msg_sender m = id \<xi>) a)"
  by inv_cterms

lemma id_constant:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, _). id \<xi> = i)"
  by inv_cterms (simp add: \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def)

lemma nhid_eq_id:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:2..PToy-:8} \<longrightarrow> nhid \<xi> = id \<xi>)"
  by inv_cterms

lemma seq_msg_ok:
  "ptoy i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<xi>, _), a, _).
                anycast (\<lambda>m. case m of Pkt num' sid' \<Rightarrow> num' = no \<xi> \<and> sid' = i | _ \<Rightarrow> True) a)"
  by (inv_cterms inv add: onl_invariant_sterms [OF toy_wf id_constant])

lemma nhid_eq_i:
  "ptoy i \<TTurnstile> onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<xi>, l). l\<in>{PToy-:2..PToy-:8} \<longrightarrow> nhid \<xi> = i)"
  proof (rule invariant_arbitraryI, clarify intro!: onlI impI)
    fix \<xi> p l n
    assume "(\<xi>, p) \<in> reachable (ptoy i) TT"
       and "l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
       and "l \<in> {PToy-:2..PToy-:8}"
    from this(1-3) have "nhid \<xi> = id \<xi>"
      by - (drule invariantD [OF nhid_eq_id], auto)
    moreover with \<open>(\<xi>, p) \<in> reachable (ptoy i) TT\<close> and \<open>l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p\<close> have "id \<xi> = i"
      by (auto dest: invariantD [OF id_constant])
    ultimately show "nhid \<xi> = i"
      by simp
  qed

subsection "Global Invariants"

lemma nos_incD [dest]:
  assumes "nos_inc \<xi> \<xi>'"
    shows "no \<xi> \<le> no \<xi>'"
  using assms unfolding nos_inc_def .

lemma nos_inc_simp [simp]:
  "nos_inc \<xi> \<xi>' = (no \<xi> \<le> no \<xi>')"
  unfolding nos_inc_def ..

lemmas oseq_nos_incs =
  open_seq_step_invariant [OF seq_nos_incs initiali_toy otoy_trans toy_trans,
                           simplified seqll_onll_swap]

lemmas oseq_no_leq_num =
  open_seq_invariant [OF seq_no_leq_num initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemma all_nos_inc:
  shows "optoy i \<Turnstile>\<^sub>A (otherwith nos_inc {i} S,
                      other nos_inc {i} \<rightarrow>)
                       onll \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>((\<sigma>, _), a, (\<sigma>', _)). (\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)))"
  proof -
    have *: "\<And>\<sigma> \<sigma>' a. \<lbrakk> otherwith nos_inc {i} S \<sigma> \<sigma>' a; no (\<sigma> i) \<le> no (\<sigma>' i) \<rbrakk>
                       \<Longrightarrow> \<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
      by (auto dest!: otherwith_syncD)
    show ?thesis
      by (inv_cterms
            inv add: oseq_step_invariant_sterms [OF oseq_nos_incs [THEN oinvariant_step_anyact]
                                                                                   toy_wf otoy_trans]
            simp add: seqllsimp) (auto elim!: *)
  qed

lemma oreceived_msg_inv:
  assumes other: "\<And>\<sigma> \<sigma>' m. \<lbrakk> P \<sigma> m; other Q {i} \<sigma> \<sigma>' \<rbrakk> \<Longrightarrow> P \<sigma>' m"
      and local: "\<And>\<sigma> m. P \<sigma> m \<Longrightarrow> P (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
    shows "optoy i \<Turnstile> (otherwith Q {i} (orecvmsg P), other Q {i} \<rightarrow>)
                       onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l \<in> {PToy-:1} \<longrightarrow> P \<sigma> (msg (\<sigma> i)))"
  proof (inv_cterms, intro impI)
    fix \<sigma> \<sigma>' l
    assume "l = PToy-:1 \<longrightarrow> P \<sigma> (msg (\<sigma> i))"
       and "l = PToy-:1"
       and "other Q {i} \<sigma> \<sigma>'"
    from this(1-2) have "P \<sigma> (msg (\<sigma> i))" ..
    hence "P \<sigma>' (msg (\<sigma> i))" using \<open>other Q {i} \<sigma> \<sigma>'\<close>
      by (rule other)
    moreover from \<open>other Q {i} \<sigma> \<sigma>'\<close> have "\<sigma>' i = \<sigma> i" ..
    ultimately show "P \<sigma>' (msg (\<sigma>' i))" by simp
  next
    fix \<sigma> \<sigma>' msg
    assume "otherwith Q {i} (orecvmsg P) \<sigma> \<sigma>' (receive msg)"
       and "\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>"
    from this(1) have "P \<sigma> msg"
                 and "\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)" by auto
    from this(1) have "P (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) msg" by (rule local)
    thus "P \<sigma>' msg"
    proof (rule other)
      from \<open>\<sigma>' i = \<sigma> i\<lparr>msg := msg\<rparr>\<close> and \<open>\<forall>j. j\<noteq>i \<longrightarrow> Q (\<sigma> j) (\<sigma>' j)\<close>
        show "other Q {i} (\<sigma>(i := \<sigma> i\<lparr>msg := msg\<rparr>)) \<sigma>'"
          by - (rule otherI, auto)
    qed
  qed

lemma msg_ok_other_nos_inc [elim]:
  assumes "msg_ok \<sigma> m"
      and "other nos_inc {i} \<sigma> \<sigma>'"
    shows "msg_ok \<sigma>' m"
  proof (cases m)
    fix num sid
    assume "m = Pkt num sid"
    with \<open>msg_ok \<sigma> m\<close> have "num \<le> no (\<sigma> sid)" by simp
    also from \<open>other nos_inc {i} \<sigma> \<sigma>'\<close> have "no (\<sigma> sid) \<le> no (\<sigma>' sid)"
      by (rule otherE) (metis eq_iff nos_incD)
    finally have "num \<le> no (\<sigma>' sid)" .
    with \<open>m = Pkt num sid\<close> show ?thesis
      by simp
  qed simp

lemma msg_ok_no_leq_no [simp, elim]:
  assumes "msg_ok \<sigma> m"
      and "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
    shows "msg_ok \<sigma>' m"
  using assms(1) proof (cases m)
    fix num sid
    assume "m = Pkt num sid"
    with \<open>msg_ok \<sigma> m\<close> have "num \<le> no (\<sigma> sid)" by simp
    also from \<open>\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)\<close> have "no (\<sigma> sid) \<le> no (\<sigma>' sid)"
      by simp
    finally have "num \<le> no (\<sigma>' sid)" .
    with \<open>m = Pkt num sid\<close> show ?thesis
      by simp
  qed (simp add: assms(1))

lemma oreceived_msg_ok:
  "optoy i \<Turnstile> (otherwith nos_inc {i} (orecvmsg msg_ok),
               other nos_inc {i} \<rightarrow>)
              onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:1..} \<longrightarrow> msg_ok \<sigma> (msg (\<sigma> i)))"
  (is "_ \<Turnstile> (?S, ?U \<rightarrow>) _")
  proof (inv_cterms inv add: oseq_step_invariant_sterms [OF all_nos_inc toy_wf otoy_trans],
         intro impI, elim impE)
    fix \<sigma> \<sigma>'
    assume "msg_ok \<sigma> (msg (\<sigma> i))"
       and other: "other nos_inc {i} \<sigma> \<sigma>'"
    moreover from other have "msg (\<sigma>' i) = msg (\<sigma> i)"
      by (clarsimp elim!: otherE)
    ultimately show "msg_ok \<sigma>' (msg (\<sigma>' i))"
      by (auto)
  next
    fix p l \<sigma> a q l' \<sigma>' pp p' m
    assume a1: "(\<sigma>', p') \<in> oreachable (optoy i) ?S ?U"
       and a2: "PToy-:1 \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p'"
       and a3: "\<sigma>' i = \<sigma> i\<lparr>msg := m\<rparr>"
    have inv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>) onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l \<in> {PToy-:1} \<longrightarrow> msg_ok \<sigma> (msg (\<sigma> i)))"
    proof (rule oreceived_msg_inv)
      fix \<sigma> \<sigma>' m
      assume "msg_ok \<sigma> m"
         and "other nos_inc {i} \<sigma> \<sigma>'"
      thus "msg_ok \<sigma>' m" ..
    next
      fix \<sigma> m
      assume "msg_ok \<sigma> m"
      thus "msg_ok (\<sigma>(i := \<sigma> i\<lparr>msg := m\<rparr>)) m"
        by (cases m) auto
    qed
    from a1 a2 a3 show "msg_ok \<sigma>' m"
      by (clarsimp dest!: oinvariantD [OF inv] onlD)
  qed simp

lemma is_pkt_handler_num_leq_no:
  shows "optoy i \<Turnstile> (otherwith nos_inc {i} (orecvmsg msg_ok),
                      other nos_inc {i} \<rightarrow>)
                    onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:6..PToy-:10} \<longrightarrow> num (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i))))"
  proof -
    { fix \<sigma> \<sigma>'
      assume "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
         and "num (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i)))"
      have "num (\<sigma> i) \<le> no (\<sigma>' (sid (\<sigma> i)))"
      proof -
        note \<open>num (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i)))\<close>
        also from \<open>\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)\<close> have "no (\<sigma> (sid (\<sigma> i))) \<le> no (\<sigma>' (sid (\<sigma> i)))"
          by auto
        finally show ?thesis .
      qed
    } note solve_step = this
    show ?thesis
    proof (inv_cterms inv add: oseq_step_invariant_sterms [OF all_nos_inc toy_wf otoy_trans]
                               onl_oinvariant_sterms [OF toy_wf oreceived_msg_ok]
                        solve: solve_step, intro impI, elim impE)
      fix \<sigma> \<sigma>'
      assume *: "num (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i)))"
         and "other nos_inc {i} \<sigma> \<sigma>'"
      from this(2) obtain "\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i"
                      and "\<forall>j. j \<notin> {i} \<longrightarrow> nos_inc (\<sigma> j) (\<sigma>' j)" ..
      show "num (\<sigma>' i) \<le> no (\<sigma>' (sid (\<sigma>' i)))"      
      proof (cases "sid (\<sigma> i) = i")
        assume "sid (\<sigma> i) = i"
        with * \<open>\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i\<close>
        show ?thesis by simp
      next
        assume "sid (\<sigma> i) \<noteq> i"
        with \<open>\<forall>j. j \<notin> {i} \<longrightarrow> nos_inc (\<sigma> j) (\<sigma>' j)\<close>
          have "no (\<sigma> (sid (\<sigma> i))) \<le> no (\<sigma>' (sid (\<sigma> i)))" by simp
        with * \<open>\<forall>i\<in>{i}. \<sigma>' i = \<sigma> i\<close>
        show ?thesis by simp
      qed
    next
      fix p l \<sigma> a q l' \<sigma>' pp p'
      assume "msg_ok \<sigma> (msg (\<sigma> i))"
         and "\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)"
         and "\<sigma>' i \<in> is_pkt (\<sigma> i)"
      show "num (\<sigma>' i) \<le> no (\<sigma>' (sid (\<sigma>' i)))"
      proof (cases "msg (\<sigma> i)")
        fix num' sid'
        assume "msg (\<sigma> i) = Pkt num' sid'"
        with \<open>\<sigma>' i \<in> is_pkt (\<sigma> i)\<close> obtain "num (\<sigma>' i) = num'"
                                      and "sid (\<sigma>' i) = sid'"
          unfolding is_pkt_def by auto
        with \<open>msg (\<sigma> i) = Pkt num' sid'\<close> and \<open>msg_ok \<sigma> (msg (\<sigma> i))\<close>
          have "num (\<sigma>' i) \<le> no (\<sigma> (sid (\<sigma>' i)))"
            by simp
        also from \<open>\<forall>j. no (\<sigma> j) \<le> no (\<sigma>' j)\<close> have "no (\<sigma> (sid (\<sigma>' i))) \<le> no (\<sigma>' (sid (\<sigma>' i)))" ..
        finally show ?thesis .
      next
        fix num' sid'
        assume "msg (\<sigma> i) = Newpkt num' sid'"
        with \<open>\<sigma>' i \<in> is_pkt (\<sigma> i)\<close> have False
          unfolding is_pkt_def by simp
        thus ?thesis ..
      qed
    qed
  qed

lemmas oseq_id_constant =
  open_seq_invariant [OF id_constant initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemmas oseq_nhid_eq_i =
  open_seq_invariant [OF nhid_eq_i initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]
  
lemmas oseq_nhid_eq_id =
  open_seq_invariant [OF nhid_eq_id initiali_toy otoy_trans toy_trans,
                      simplified seql_onl_swap]

lemma oseq_bigger_than_next:
  shows "optoy i \<Turnstile> (otherwith nos_inc {i} (orecvmsg msg_ok),
                      other nos_inc {i} \<rightarrow>) global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
    (is "_ \<Turnstile> (?S, ?U \<rightarrow>) ?P")
  proof -
    have nhidinv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>)
                              onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). l\<in>{PToy-:2..PToy-:8}
                                                    \<longrightarrow> nhid (\<sigma> i) = id (\<sigma> i))"
      by (rule oinvariant_weakenE [OF oseq_nhid_eq_id]) (auto simp: seqlsimp)
    have idinv: "optoy i \<Turnstile> (?S, ?U \<rightarrow>) onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). id (\<sigma> i) = i)"
      by (rule oinvariant_weakenE [OF oseq_id_constant]) (auto simp: seqlsimp)
    { fix \<sigma> \<sigma>' a
      assume "no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i)))"
         and "\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)"
      note this(1)
      also from \<open>\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)\<close> have "no (\<sigma> (nhid (\<sigma> i))) \<le> no (\<sigma>' (nhid (\<sigma> i)))"
        by auto
      finally have "no (\<sigma> i) \<le> no (\<sigma>' (nhid (\<sigma> i)))" ..
    } note * = this
    have "optoy i \<Turnstile> (otherwith nos_inc {i} (orecvmsg msg_ok),
                      other nos_inc {i} \<rightarrow>)
                     onl \<Gamma>\<^sub>T\<^sub>O\<^sub>Y (\<lambda>(\<sigma>, l). no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
    proof (inv_cterms
             inv add: onl_oinvariant_sterms [OF toy_wf oseq_no_leq_num [THEN oinvariant_anyact]]
                      oseq_step_invariant_sterms [OF all_nos_inc toy_wf otoy_trans]
                      onl_oinvariant_sterms [OF toy_wf is_pkt_handler_num_leq_no]
                      onl_oinvariant_sterms [OF toy_wf nhidinv]
                      onl_oinvariant_sterms [OF toy_wf idinv]
             simp add: seqlsimp seqllsimp
             simp del: nos_inc_simp
                solve: *)
      fix \<sigma> p l
      assume "(\<sigma>, p) \<in> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y"
      thus "no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i)))"
        by (simp add: \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def)
    next
      fix \<sigma> \<sigma>' p l
      assume or: "(\<sigma>, p) \<in> oreachable (optoy i) ?S ?U"
         and "l \<in> labels \<Gamma>\<^sub>T\<^sub>O\<^sub>Y p"
         and "no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i)))"
         and "other nos_inc {i} \<sigma> \<sigma>'"
      show "no (\<sigma>' i) \<le> no (\<sigma>' (nhid (\<sigma>' i)))"
      proof (cases "nhid (\<sigma>' i) = i")
        assume "nhid (\<sigma>' i) = i"
        with \<open>no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i)))\<close> show ?thesis
          by simp
      next
        assume "nhid (\<sigma>' i) \<noteq> i"
        moreover from \<open>other nos_inc {i} \<sigma> \<sigma>'\<close> [THEN other_localD] have "\<sigma>' i = \<sigma> i"
          by simp
        ultimately have "no (\<sigma> (nhid (\<sigma> i))) \<le> no (\<sigma>' (nhid (\<sigma>' i)))"
          using \<open>other nos_inc {i} \<sigma> \<sigma>'\<close> and \<open>\<sigma>' i = \<sigma> i\<close> by (auto)
        with \<open>no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i)))\<close> and \<open>\<sigma>' i = \<sigma> i\<close> show ?thesis
          by simp
      qed
    next
      fix p l \<sigma> a q l' \<sigma>' pp p'
      assume "no (\<sigma> i) \<le> num (\<sigma> i)"
         and "num (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i)))"
         and "\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)"
      from this(1-2) have "no (\<sigma> i) \<le> no (\<sigma> (sid (\<sigma> i)))"
        by (rule le_trans)
      also from \<open>\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)\<close>
        have "no (\<sigma> (sid (\<sigma> i))) \<le> no (\<sigma>' (sid (\<sigma> i)))"
          by auto
      finally show "no (\<sigma> i) \<le> no (\<sigma>' (sid (\<sigma> i)))" ..
    qed
    thus ?thesis
      by (rule oinvariant_weakenE)
         (auto simp: onl_def)
  qed

lemma anycast_weakenE [elim]:
  assumes "anycast P a"
      and "\<And>m. P m \<Longrightarrow> Q m"
  shows "anycast Q a"
  using assms unfolding anycast_def
  by (auto split: seq_action.split)

lemma oseq_msg_ok:
  "optoy i \<Turnstile>\<^sub>A (act TT, other U {i} \<rightarrow>) globala (\<lambda>(\<sigma>, a, _). anycast (msg_ok \<sigma>) a)"
  by (rule ostep_invariant_weakenE [OF open_seq_step_invariant
            [OF seq_msg_ok initiali_toy otoy_trans toy_trans, simplified seql_onl_swap]])
     (auto simp: seqllsimp dest!: onllD elim!: anycast_weakenE intro!: msg_okI)

subsection "Lifting"

lemma opar_bigger_than_next:
  shows "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile> (otherwith nos_inc {i} (orecvmsg msg_ok),
                      other nos_inc {i} \<rightarrow>) global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
  proof (rule lift_into_qmsg [OF oseq_bigger_than_next])
    fix \<sigma> \<sigma>' m
    assume "\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)"
       and "msg_ok \<sigma> m"
    from this(2) show "msg_ok \<sigma>' m"
    proof (cases m, simp only: msg_ok_Pkt)
      fix num' sid'
      assume "num' \<le> no (\<sigma> sid')"
      also from \<open>\<forall>j. nos_inc (\<sigma> j) (\<sigma>' j)\<close> have "no (\<sigma> sid') \<le> no (\<sigma>' sid')"
        by simp
      finally show "num' \<le> no (\<sigma>' sid')" .
    qed simp
  next
    show "optoy i \<Turnstile>\<^sub>A (otherwith nos_inc {i} (orecvmsg msg_ok), other nos_inc {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_inc (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF open_seq_step_invariant
                                         [OF seq_nos_incs initiali_toy otoy_trans toy_trans]])
         (auto simp: seqllsimp dest!: onllD)
  qed simp

lemma onode_bigger_than_next:
  "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o
     \<Turnstile> (otherwith nos_inc {i} (oarrivemsg msg_ok), other nos_inc {i} \<rightarrow>)
        global (\<lambda>\<sigma>. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
  by (rule node_lift [OF opar_bigger_than_next])

lemma node_local_nos_inc:
  "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                     globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_inc (\<sigma> i) (\<sigma>' i))"
  proof (rule node_lift_step_statelessassm)
    have "optoy i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                      globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_inc (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF oseq_nos_incs])
         (auto simp: seqllsimp dest!: onllD)
    thus "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                globala (\<lambda>(\<sigma>, _, \<sigma>'). nos_inc (\<sigma> i) (\<sigma>' i))"
      by (rule lift_step_into_qmsg_statelessassm) auto
  qed simp

lemma opnet_bigger_than_next:
  "opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n
     \<Turnstile> (otherwith nos_inc (net_tree_ips n) (oarrivemsg msg_ok),
         other nos_inc (net_tree_ips n) \<rightarrow>)
        global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
  proof (rule pnet_lift [OF onode_bigger_than_next])
    fix i R\<^sub>i
    have "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_ok \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                            globala (\<lambda>(\<sigma>, a, _). castmsg (msg_ok \<sigma>) a)"
    proof (rule node_lift_anycast_statelessassm)
      have "optoy i \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                        globala (\<lambda>(\<sigma>, a, _). anycast (msg_ok \<sigma>) a)"
        by (rule ostep_invariant_weakenE [OF oseq_msg_ok]) auto
      hence "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg (\<lambda>_ _. True) \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                   globala (\<lambda>(\<sigma>, a, _). anycast (msg_ok \<sigma>) a)"
        by (rule lift_step_into_qmsg_statelessassm) auto
      thus "optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. orecvmsg msg_ok \<sigma>, other (\<lambda>_ _. True) {i} \<rightarrow>)
                                  globala (\<lambda>(\<sigma>, a, _). anycast (msg_ok \<sigma>) a)"
        by (rule ostep_invariant_weakenE) auto
    qed
    thus "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_ok \<sigma>, other nos_inc {i} \<rightarrow>)
                                            globala (\<lambda>(\<sigma>, a, _). castmsg (msg_ok \<sigma>) a)"
      by (rule ostep_invariant_weakenE) auto
  next
    fix i R\<^sub>i
    show "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<^sub>i\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_ok \<sigma>,
                                            other nos_inc {i} \<rightarrow>)
             globala (\<lambda>(\<sigma>, a, \<sigma>'). a \<noteq> \<tau> \<and> (\<forall>d. a \<noteq> i:deliver(d)) \<longrightarrow> nos_inc (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF node_local_nos_inc]) auto
  next
    fix i R
    show "\<langle>i : optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg : R\<rangle>\<^sub>o \<Turnstile>\<^sub>A (\<lambda>\<sigma> _. oarrivemsg msg_ok \<sigma>,
                                           other nos_inc {i} \<rightarrow>)
             globala (\<lambda>(\<sigma>, a, \<sigma>'). a = \<tau> \<or> (\<exists>d. a = i:deliver(d)) \<longrightarrow> nos_inc (\<sigma> i) (\<sigma>' i))"
      by (rule ostep_invariant_weakenE [OF node_local_nos_inc]) auto
  qed simp_all

lemma ocnet_bigger_than_next:
  "oclosed (opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n)
     \<Turnstile> (\<lambda>_ _ _. True, other nos_inc (net_tree_ips n) \<rightarrow>)
        global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
  proof (rule inclosed_closed)
    show "opnet (\<lambda>i. optoy i \<langle>\<langle>\<^bsub>i\<^esub> qmsg) n
            \<Turnstile> (otherwith (=) (net_tree_ips n) inoclosed, other nos_inc (net_tree_ips n) \<rightarrow>)
               global (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
    proof (rule oinvariant_weakenE [OF opnet_bigger_than_next])
      fix s s':: "nat \<Rightarrow> state" and a :: "msg node_action"
      assume "otherwith (=) (net_tree_ips n) inoclosed s s' a"
      thus "otherwith nos_inc (net_tree_ips n) (oarrivemsg msg_ok) s s' a"
      proof (rule otherwithE, intro otherwithI)
        assume "inoclosed s a"
           and "\<forall>j. j \<notin> net_tree_ips n \<longrightarrow> s j = s' j"
           and "otherwith ((=)) (net_tree_ips n) inoclosed s s' a"
        thus "oarrivemsg msg_ok s a"
          by (cases a) auto
      qed auto
    qed simp
  qed

subsection "Transfer"

definition
  initmissing :: "(nat \<Rightarrow> state option) \<times> 'a \<Rightarrow> (nat \<Rightarrow> state) \<times> 'a"
where
  "initmissing \<sigma> = (\<lambda>i. case (fst \<sigma>) i of None \<Rightarrow> toy_init i | Some s \<Rightarrow> s, snd \<sigma>)"

lemma not_in_net_ips_fst_init_missing [simp]:
  assumes "i \<notin> net_ips \<sigma>"
    shows "fst (initmissing (netgmap fst \<sigma>)) i = toy_init i"
  using assms unfolding initmissing_def by simp

lemma fst_initmissing_netgmap_pair_fst [simp]:
  "fst (initmissing (netgmap (\<lambda>(p, q). (fst (Fun.id p), snd (Fun.id p), q)) s))
                                               = fst (initmissing (netgmap fst s))"
  unfolding initmissing_def by auto

interpretation toy_openproc: openproc ptoy optoy Fun.id
  rewrites "toy_openproc.initmissing = initmissing"
  proof -
    show "openproc ptoy optoy Fun.id"
    proof unfold_locales
      fix i :: ip
      have "{(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> \<sigma>\<^sub>T\<^sub>O\<^sub>Y i \<and> (\<forall>j. j \<noteq> i \<longrightarrow> \<sigma> j \<in> fst ` \<sigma>\<^sub>T\<^sub>O\<^sub>Y j)} \<subseteq> \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y"
        unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>O\<^sub>T\<^sub>O\<^sub>Y_def
        proof (rule equalityD1)
          show "\<And>f p. {(\<sigma>, \<zeta>). (\<sigma> i, \<zeta>) \<in> {(f i, p)} \<and> (\<forall>j. j \<noteq> i
                      \<longrightarrow> \<sigma> j \<in> fst ` {(f j, p)})} = {(f, p)}"
            by (rule set_eqI) auto
        qed
      thus "{ (\<sigma>, \<zeta>) |\<sigma> \<zeta> s. s \<in> init (ptoy i)
                             \<and> (\<sigma> i, \<zeta>) = Fun.id s
                             \<and> (\<forall>j. j\<noteq>i \<longrightarrow> \<sigma> j \<in> (fst o Fun.id) ` init (ptoy j)) } \<subseteq> init (optoy i)"
        by simp
    next
      show "\<forall>j. init (ptoy j) \<noteq> {}"
        unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp
    next
      fix i s a s' \<sigma> \<sigma>'
      assume "\<sigma> i = fst (Fun.id s)"
         and "\<sigma>' i = fst (Fun.id s')"
         and "(s, a, s') \<in> trans (ptoy i)"
      then obtain q q' where "s = (\<sigma> i, q)"
                         and "s' = (\<sigma>' i, q')"
                         and "((\<sigma> i, q), a, (\<sigma>' i, q')) \<in> trans (ptoy i)" 
         by (cases s, cases s') auto
      from this(3) have "((\<sigma>, q), a, (\<sigma>', q')) \<in> trans (optoy i)"
        by simp (rule open_seqp_action [OF toy_wf])

      with \<open>s = (\<sigma> i, q)\<close> and \<open>s' = (\<sigma>' i, q')\<close>
        show "((\<sigma>, snd (Fun.id s)), a, (\<sigma>', snd (Fun.id s'))) \<in> trans (optoy i)"
          by simp
    qed
    then interpret op0: openproc ptoy optoy Fun.id .
    have [simp]: "\<And>i. (SOME x. x \<in> (fst o Fun.id) ` init (ptoy i)) = toy_init i"
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def by simp
    hence "\<And>i. openproc.initmissing ptoy Fun.id i = initmissing i"
      unfolding op0.initmissing_def op0.someinit_def initmissing_def
      by (auto split: option.split)
    thus "openproc.initmissing ptoy Fun.id = initmissing" ..
  qed

lemma fst_initmissing_netgmap_default_toy_init_netlift:
  "fst (initmissing (netgmap sr s)) = default toy_init (netlift sr s)"
  unfolding initmissing_def default_def
  by (simp add: fst_netgmap_netlift del: One_nat_def)

definition
  netglobal :: "((nat \<Rightarrow> state) \<Rightarrow> bool) \<Rightarrow> ((state \<times> 'b) \<times> 'c) net_state \<Rightarrow> bool"
where
  "netglobal P \<equiv> (\<lambda>s. P (default toy_init (netlift fst s)))"

interpretation toy_openproc_par_qmsg: openproc_parq ptoy optoy Fun.id qmsg
  rewrites "toy_openproc_par_qmsg.netglobal = netglobal"
    and "toy_openproc_par_qmsg.initmissing = initmissing"
  proof -
    show "openproc_parq ptoy optoy Fun.id qmsg"
      by (unfold_locales) simp
    then interpret opq: openproc_parq ptoy optoy Fun.id qmsg .

    have im: "\<And>\<sigma>. openproc.initmissing (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (Fun.id p), snd (Fun.id p), q)) \<sigma>
                                                                                    = initmissing \<sigma>"
      unfolding opq.initmissing_def opq.someinit_def initmissing_def
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def by (clarsimp cong: option.case_cong)
    thus "openproc.initmissing (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (Fun.id p), snd (Fun.id p), q)) = initmissing"
      by (rule ext)

    have "\<And>P \<sigma>. openproc.netglobal (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (Fun.id p), snd (Fun.id p), q)) P \<sigma>
                                                                                = netglobal P \<sigma>"
      unfolding opq.netglobal_def netglobal_def opq.initmissing_def initmissing_def opq.someinit_def
      unfolding \<sigma>\<^sub>T\<^sub>O\<^sub>Y_def \<sigma>\<^sub>Q\<^sub>M\<^sub>S\<^sub>G_def
      by (clarsimp cong: option.case_cong
                   simp del: One_nat_def
                   simp add: fst_initmissing_netgmap_default_toy_init_netlift
                                                  [symmetric, unfolded initmissing_def])
    thus "openproc.netglobal (\<lambda>i. ptoy i \<langle>\<langle> qmsg) (\<lambda>(p, q). (fst (Fun.id p), snd (Fun.id p), q)) = netglobal"
      by auto
  qed

subsection "Final result"

lemma bigger_than_next:
  assumes "wf_net_tree n"
  shows "closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) n) \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
        (is "_ \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i. ?inv \<sigma> i)")
  proof -
    from \<open>wf_net_tree n\<close>
      have proto: "closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) n)
                      \<TTurnstile> netglobal (\<lambda>\<sigma>. \<forall>i\<in>net_tree_ips n. no (\<sigma> i) \<le> no (\<sigma> (nhid (\<sigma> i))))"
        by (rule toy_openproc_par_qmsg.close_opnet [OF _ ocnet_bigger_than_next])
    show ?thesis
    unfolding invariant_def opnet_sos.opnet_tau1
    proof (rule, simp only: toy_openproc_par_qmsg.netglobalsimp
                            fst_initmissing_netgmap_pair_fst, rule allI)
      fix \<sigma> i
      assume sr: "\<sigma> \<in> reachable (closed (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) n)) TT"
      hence "\<forall>i\<in>net_tree_ips n. ?inv (fst (initmissing (netgmap fst \<sigma>))) i"
        by - (drule invariantD [OF proto],
              simp only: toy_openproc_par_qmsg.netglobalsimp
                         fst_initmissing_netgmap_pair_fst)
      thus "?inv (fst (initmissing (netgmap fst \<sigma>))) i"
      proof (cases "i\<in>net_tree_ips n")
        assume "i\<notin>net_tree_ips n"
        from sr have "\<sigma> \<in> reachable (pnet (\<lambda>i. ptoy i \<langle>\<langle> qmsg) n) TT" ..
        hence "net_ips \<sigma> = net_tree_ips n" ..
        with \<open>i\<notin>net_tree_ips n\<close> have "i\<notin>net_ips \<sigma>" by simp
        hence "(fst (initmissing (netgmap fst \<sigma>))) i = toy_init i"
          by simp
        thus ?thesis by simp
      qed metis
    qed
  qed

end
