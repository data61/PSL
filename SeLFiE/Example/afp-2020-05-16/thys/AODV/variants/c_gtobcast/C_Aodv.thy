(*  Title:       variants/c_gtobcast/Aodv.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "The AODV protocol"

theory C_Aodv
imports C_Aodv_Data C_Aodv_Message
        AWN.AWN_SOS_Labels AWN.AWN_Invariants
begin

subsection "Data state"

record state =
  ip    :: "ip"
  sn    :: "sqn"
  rt    :: "rt" 
  rreqs :: "(ip \<times> rreqid) set"
  store :: "store"
  (* all locals *)
  msg    :: "msg"
  data   :: "data"
  dests  :: "ip \<rightharpoonup> sqn"
  rreqid :: "rreqid"
  dip    :: "ip"
  oip    :: "ip"
  hops   :: "nat"
  dsn    :: "sqn"
  dsk    :: "k"
  osn    :: "sqn"
  sip    :: "ip"

abbreviation aodv_init :: "ip \<Rightarrow> state"
where "aodv_init i \<equiv> \<lparr>
         ip = i,
         sn = 1,
         rt = Map.empty,
         rreqs = {},
         store = Map.empty,

         msg    = (SOME x. True),
         data   = (SOME x. True),
         dests  = (SOME x. True),
         rreqid = (SOME x. True),
         dip    = (SOME x. True),
         oip    = (SOME x. True),
         hops   = (SOME x. True),
         dsn    = (SOME x. True),
         dsk    = (SOME x. True),
         osn    = (SOME x. True),
         sip    = (SOME x. x \<noteq> i)
       \<rparr>"

lemma some_neq_not_eq [simp]: "\<not>((SOME x :: nat. x \<noteq> i) = i)"
  by (subst some_eq_ex) (metis zero_neq_numeral)

definition clear_locals :: "state \<Rightarrow> state"
where "clear_locals \<xi> = \<xi> \<lparr>
    msg    := (SOME x. True),
    data   := (SOME x. True),
    dests  := (SOME x. True),
    rreqid := (SOME x. True),
    dip    := (SOME x. True),
    oip    := (SOME x. True),
    hops   := (SOME x. True),
    dsn    := (SOME x. True),
    dsk    := (SOME x. True),
    osn    := (SOME x. True),
    sip    := (SOME x. x \<noteq> ip \<xi>)
  \<rparr>"

lemma clear_locals_sip_not_ip [simp]: "\<not>(sip (clear_locals \<xi>) = ip \<xi>)"
  unfolding clear_locals_def by simp

lemma clear_locals_but_not_globals [simp]:
  "ip (clear_locals \<xi>) = ip \<xi>"
  "sn (clear_locals \<xi>) = sn \<xi>"
  "rt (clear_locals \<xi>) = rt \<xi>"
  "rreqs (clear_locals \<xi>) = rreqs \<xi>"
  "store (clear_locals \<xi>) = store \<xi>"
  unfolding clear_locals_def by auto

subsection "Auxilliary message handling definitions"

definition is_newpkt
where "is_newpkt \<xi> \<equiv> case msg \<xi> of
                       Newpkt data' dip' \<Rightarrow> { \<xi>\<lparr>data := data', dip := dip'\<rparr> }
                     | _ \<Rightarrow> {}"

definition is_pkt
where "is_pkt \<xi> \<equiv> case msg \<xi> of
                    Pkt data' dip' oip' \<Rightarrow> { \<xi>\<lparr> data := data', dip := dip', oip := oip' \<rparr> }
                  | _ \<Rightarrow> {}"

definition is_rreq
where "is_rreq \<xi> \<equiv> case msg \<xi> of
                     Rreq hops' rreqid' dip' dsn' dsk' oip' osn' sip' \<Rightarrow>
                       { \<xi>\<lparr> hops := hops', rreqid := rreqid', dip := dip', dsn := dsn',
                            dsk := dsk', oip := oip', osn := osn', sip := sip' \<rparr> }
                   | _ \<Rightarrow> {}"

lemma is_rreq_asm [dest!]:
  assumes "\<xi>' \<in> is_rreq \<xi>"
    shows "(\<exists>hops' rreqid' dip' dsn' dsk' oip' osn' sip'.
               msg \<xi> = Rreq hops' rreqid' dip' dsn' dsk' oip' osn' sip' \<and>
               \<xi>' = \<xi>\<lparr> hops := hops', rreqid := rreqid', dip := dip', dsn := dsn',
                       dsk := dsk', oip := oip', osn := osn', sip := sip' \<rparr>)"
  using assms unfolding is_rreq_def
  by (cases "msg \<xi>") simp_all

definition is_rrep
where "is_rrep \<xi> \<equiv> case msg \<xi> of
                     Rrep hops' dip' dsn' oip' sip' \<Rightarrow>
                       { \<xi>\<lparr> hops := hops', dip := dip', dsn := dsn', oip := oip', sip := sip' \<rparr> }
                   | _ \<Rightarrow> {}"

lemma is_rrep_asm [dest!]:
  assumes "\<xi>' \<in> is_rrep \<xi>"
    shows "(\<exists>hops' dip' dsn' oip' sip'.
               msg \<xi> = Rrep hops' dip' dsn' oip' sip' \<and>
               \<xi>' = \<xi>\<lparr> hops := hops', dip := dip', dsn := dsn', oip := oip', sip := sip' \<rparr>)"
  using assms unfolding is_rrep_def
  by (cases "msg \<xi>") simp_all

definition is_rerr
where "is_rerr \<xi> \<equiv> case msg \<xi> of
                     Rerr dests' sip' \<Rightarrow> { \<xi>\<lparr> dests := dests', sip := sip' \<rparr> }
                   | _ \<Rightarrow> {}"

lemma is_rerr_asm [dest!]:
  assumes "\<xi>' \<in> is_rerr \<xi>"
    shows "(\<exists>dests' sip'.
               msg \<xi> = Rerr dests' sip' \<and>
               \<xi>' = \<xi>\<lparr> dests := dests', sip := sip' \<rparr>)"
  using assms unfolding is_rerr_def
  by (cases "msg \<xi>") simp_all

lemmas is_msg_defs =
  is_rerr_def is_rrep_def is_rreq_def is_pkt_def is_newpkt_def

lemma is_msg_inv_ip [simp]:
  "\<xi>' \<in> is_rerr \<xi>   \<Longrightarrow> ip \<xi>' = ip \<xi>"
  "\<xi>' \<in> is_rrep \<xi>   \<Longrightarrow> ip \<xi>' = ip \<xi>"
  "\<xi>' \<in> is_rreq \<xi>   \<Longrightarrow> ip \<xi>' = ip \<xi>"
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> ip \<xi>' = ip \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> ip \<xi>' = ip \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_sn [simp]:
  "\<xi>' \<in> is_rerr \<xi>   \<Longrightarrow> sn \<xi>' = sn \<xi>"
  "\<xi>' \<in> is_rrep \<xi>   \<Longrightarrow> sn \<xi>' = sn \<xi>"
  "\<xi>' \<in> is_rreq \<xi>   \<Longrightarrow> sn \<xi>' = sn \<xi>"
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> sn \<xi>' = sn \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> sn \<xi>' = sn \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_rt [simp]:
  "\<xi>' \<in> is_rerr \<xi>   \<Longrightarrow> rt \<xi>' = rt \<xi>"
  "\<xi>' \<in> is_rrep \<xi>   \<Longrightarrow> rt \<xi>' = rt \<xi>"
  "\<xi>' \<in> is_rreq \<xi>   \<Longrightarrow> rt \<xi>' = rt \<xi>"
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> rt \<xi>' = rt \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> rt \<xi>' = rt \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_rreqs [simp]:
  "\<xi>' \<in> is_rerr \<xi>   \<Longrightarrow> rreqs \<xi>' = rreqs \<xi>"
  "\<xi>' \<in> is_rrep \<xi>   \<Longrightarrow> rreqs \<xi>' = rreqs \<xi>"
  "\<xi>' \<in> is_rreq \<xi>   \<Longrightarrow> rreqs \<xi>' = rreqs \<xi>"
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> rreqs \<xi>' = rreqs \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> rreqs \<xi>' = rreqs \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_store [simp]:
  "\<xi>' \<in> is_rerr \<xi>   \<Longrightarrow> store \<xi>' = store \<xi>"
  "\<xi>' \<in> is_rrep \<xi>   \<Longrightarrow> store \<xi>' = store \<xi>"
  "\<xi>' \<in> is_rreq \<xi>   \<Longrightarrow> store \<xi>' = store \<xi>"
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> store \<xi>' = store \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> store \<xi>' = store \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

lemma is_msg_inv_sip [simp]:
  "\<xi>' \<in> is_pkt \<xi>    \<Longrightarrow> sip \<xi>' = sip \<xi>"
  "\<xi>' \<in> is_newpkt \<xi> \<Longrightarrow> sip \<xi>' = sip \<xi>"
  unfolding is_msg_defs
  by (cases "msg \<xi>", clarsimp+)+

subsection "The protocol process"

datatype pseqp =
    PAodv
  | PNewPkt
  | PPkt
  | PRreq
  | PRrep
  | PRerr

fun nat_of_seqp :: "pseqp \<Rightarrow> nat"
where
  "nat_of_seqp PAodv  = 1"
| "nat_of_seqp PPkt   = 2"
| "nat_of_seqp PNewPkt   = 3"
| "nat_of_seqp PRreq  = 4"
| "nat_of_seqp PRrep  = 5"
| "nat_of_seqp PRerr  = 6"

instantiation "pseqp" :: ord
begin
definition less_eq_seqp [iff]: "l1 \<le> l2 = (nat_of_seqp l1 \<le> nat_of_seqp l2)"
definition less_seqp [iff]:    "l1 < l2 = (nat_of_seqp l1 < nat_of_seqp l2)"
instance ..
end

abbreviation AODV
where
  "AODV \<equiv> \<lambda>_. \<lbrakk>clear_locals\<rbrakk> call(PAodv)"

abbreviation PKT
where
  "PKT args \<equiv>

     \<lbrakk>\<xi>. let (data, dip, oip) = args \<xi> in
         (clear_locals \<xi>) \<lparr> data := data, dip := dip, oip := oip \<rparr>\<rbrakk>
     call(PPkt)"
abbreviation NEWPKT
where
  "NEWPKT args \<equiv>
     \<lbrakk>\<xi>. let (data, dip) = args \<xi> in
         (clear_locals \<xi>) \<lparr> data := data, dip := dip \<rparr>\<rbrakk>
     call(PNewPkt)"

abbreviation RREQ
where
  "RREQ args \<equiv>
     \<lbrakk>\<xi>. let (hops, rreqid, dip, dsn, dsk, oip, osn, sip) = args \<xi> in
         (clear_locals \<xi>) \<lparr> hops := hops, rreqid := rreqid, dip := dip,
                            dsn := dsn, dsk := dsk, oip := oip,
                            osn := osn, sip := sip \<rparr>\<rbrakk>
     call(PRreq)"

abbreviation RREP
where
  "RREP args \<equiv>
     \<lbrakk>\<xi>. let (hops, dip, dsn, oip, sip) = args \<xi> in
         (clear_locals \<xi>) \<lparr> hops := hops, dip := dip, dsn := dsn,
                            oip := oip, sip := sip \<rparr>\<rbrakk>
     call(PRrep)"

abbreviation RERR
where
  "RERR args \<equiv>
     \<lbrakk>\<xi>. let (dests, sip) = args \<xi> in
         (clear_locals \<xi>) \<lparr> dests := dests, sip := sip \<rparr>\<rbrakk>
     call(PRerr)"

fun \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V :: "(state, msg, pseqp, pseqp label) seqp_env"
where
  "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PAodv = labelled PAodv (
     receive(\<lambda>msg' \<xi>. \<xi> \<lparr> msg := msg' \<rparr>).
     (    \<langle>is_newpkt\<rangle> NEWPKT(\<lambda>\<xi>. (data \<xi>, ip \<xi>))
       \<oplus> \<langle>is_pkt\<rangle> PKT(\<lambda>\<xi>. (data \<xi>, dip \<xi>, oip \<xi>))
       \<oplus> \<langle>is_rreq\<rangle>
            \<lbrakk>\<xi>. \<xi> \<lparr>rt := update (rt \<xi>) (sip \<xi>) (0, unk, val, 1, sip \<xi>) \<rparr>\<rbrakk>
            RREQ(\<lambda>\<xi>. (hops \<xi>, rreqid \<xi>, dip \<xi>, dsn \<xi>, dsk \<xi>, oip \<xi>, osn \<xi>, sip \<xi>))
       \<oplus> \<langle>is_rrep\<rangle>
            \<lbrakk>\<xi>. \<xi> \<lparr>rt := update (rt \<xi>) (sip \<xi>) (0, unk, val, 1, sip \<xi>) \<rparr>\<rbrakk>
            RREP(\<lambda>\<xi>. (hops \<xi>, dip \<xi>, dsn \<xi>, oip \<xi>, sip \<xi>))
       \<oplus> \<langle>is_rerr\<rangle>
            \<lbrakk>\<xi>. \<xi> \<lparr>rt := update (rt \<xi>) (sip \<xi>) (0, unk, val, 1, sip \<xi>) \<rparr>\<rbrakk>
            RERR(\<lambda>\<xi>. (dests \<xi>, sip \<xi>))
     )
     \<oplus> \<langle>\<lambda>\<xi>. { \<xi>\<lparr> dip := dip \<rparr> | dip. dip \<in> qD(store \<xi>) \<inter> vD(rt \<xi>) }\<rangle>
          \<lbrakk>\<xi>. \<xi> \<lparr> data := hd(\<sigma>\<^bsub>queue\<^esub>(store \<xi>, dip \<xi>)) \<rparr>\<rbrakk>
          unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (dip \<xi>)), \<lambda>\<xi>. pkt(data \<xi>, dip \<xi>, ip \<xi>)).
            \<lbrakk>\<xi>. \<xi> \<lparr> store := the (drop (dip \<xi>) (store \<xi>)) \<rparr>\<rbrakk>
            AODV()
          \<triangleright> \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. if (rip \<in> vD (rt \<xi>) \<and> nhop (rt \<xi>) rip = nhop (rt \<xi>) (dip \<xi>))
                                     then Some (inc (sqn (rt \<xi>) rip)) else None) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)). AODV()
     \<oplus> \<langle>\<lambda>\<xi>. { \<xi>\<lparr> dip := dip \<rparr>
             | dip. dip \<in> qD(store \<xi>) - vD(rt \<xi>) \<and> the (\<sigma>\<^bsub>p-flag\<^esub>(store \<xi>, dip)) = req }\<rangle>
         \<lbrakk>\<xi>. \<xi> \<lparr> store := unsetRRF (store \<xi>) (dip \<xi>) \<rparr>\<rbrakk>
         \<lbrakk>\<xi>. \<xi> \<lparr> sn := inc (sn \<xi>) \<rparr>\<rbrakk>
         \<lbrakk>\<xi>. \<xi> \<lparr> rreqid := nrreqid (rreqs \<xi>) (ip \<xi>) \<rparr>\<rbrakk>
         \<lbrakk>\<xi>. \<xi> \<lparr> rreqs := rreqs \<xi> \<union> {(ip \<xi>, rreqid \<xi>)} \<rparr>\<rbrakk>
         broadcast(\<lambda>\<xi>. rreq(0, rreqid \<xi>, dip \<xi>, sqn (rt \<xi>) (dip \<xi>), sqnf (rt \<xi>) (dip \<xi>), ip \<xi>, sn \<xi>,
                            ip \<xi>)). AODV())"

|  "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PNewPkt = labelled PNewPkt (
     \<langle>\<xi>. dip \<xi> = ip \<xi>\<rangle>
        deliver(\<lambda>\<xi>. data \<xi>).AODV()
     \<oplus> \<langle>\<xi>. dip \<xi> \<noteq> ip \<xi>\<rangle>
        \<lbrakk>\<xi>. \<xi> \<lparr> store := add (data \<xi>) (dip \<xi>) (store \<xi>) \<rparr>\<rbrakk>
        AODV())"

| "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PPkt = labelled PPkt (
     \<langle>\<xi>. dip \<xi> = ip \<xi>\<rangle>
        deliver(\<lambda>\<xi>. data \<xi>).AODV()
     \<oplus> \<langle>\<xi>. dip \<xi> \<noteq> ip \<xi>\<rangle>
     (
       \<langle>\<xi>. dip \<xi> \<in> vD (rt \<xi>)\<rangle>
         unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (dip \<xi>)), \<lambda>\<xi>. pkt(data \<xi>, dip \<xi>, oip \<xi>)).AODV()
         \<triangleright>
           \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. if (rip \<in> vD (rt \<xi>) \<and> nhop (rt \<xi>) rip = nhop (rt \<xi>) (dip \<xi>))
                                   then Some (inc (sqn (rt \<xi>) rip)) else None) \<rparr>\<rbrakk>
           \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
           \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
           broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)).AODV()
       \<oplus> \<langle>\<xi>. dip \<xi> \<notin> vD (rt \<xi>)\<rangle>
       (
           \<langle>\<xi>. dip \<xi> \<in> iD (rt \<xi>)\<rangle>
             broadcast(\<lambda>\<xi>. rerr([dip \<xi> \<mapsto> sqn (rt \<xi>) (dip \<xi>)], ip \<xi>)). AODV()
           \<oplus> \<langle>\<xi>. dip \<xi> \<notin> iD (rt \<xi>)\<rangle>
              AODV()
       )
     ))"

| "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRreq = labelled PRreq (
     \<langle>\<xi>. (oip \<xi>, rreqid \<xi>) \<in> rreqs \<xi>\<rangle>
       AODV()
     \<oplus> \<langle>\<xi>. (oip \<xi>, rreqid \<xi>) \<notin> rreqs \<xi>\<rangle>
       \<lbrakk>\<xi>. \<xi> \<lparr> rt := update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, hops \<xi> + 1, sip \<xi>) \<rparr>\<rbrakk>
       \<lbrakk>\<xi>. \<xi> \<lparr> rreqs := rreqs \<xi> \<union> {(oip \<xi>, rreqid \<xi>)} \<rparr>\<rbrakk>
       (
         \<langle>\<xi>. dip \<xi> = ip \<xi>\<rangle>
           \<lbrakk>\<xi>. \<xi> \<lparr> sn := max (sn \<xi>) (dsn \<xi>) \<rparr>\<rbrakk>
           unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (oip \<xi>)), \<lambda>\<xi>. rrep(0, dip \<xi>, sn \<xi>, oip \<xi>, ip \<xi>)).AODV()
           \<triangleright>
             \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. if (rip \<in> vD (rt \<xi>) \<and> nhop (rt \<xi>) rip = nhop (rt \<xi>) (oip \<xi>))
                                     then Some (inc (sqn (rt \<xi>) rip)) else None) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)).AODV()
         \<oplus> \<langle>\<xi>. dip \<xi> \<noteq> ip \<xi>\<rangle>
         (
           \<langle>\<xi>. dip \<xi> \<in> vD (rt \<xi>) \<and> dsn \<xi> \<le> sqn (rt \<xi>) (dip \<xi>) \<and> sqnf (rt \<xi>) (dip \<xi>) = kno\<rangle>
             unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (oip \<xi>)), \<lambda>\<xi>. rrep(the (dhops (rt \<xi>) (dip \<xi>)), dip \<xi>,
                                                             sqn (rt \<xi>) (dip \<xi>), oip \<xi>, ip \<xi>)).
             AODV()
           \<triangleright>
             \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. if (rip \<in> vD (rt \<xi>) \<and> nhop (rt \<xi>) rip = nhop (rt \<xi>) (oip \<xi>))
                                     then Some (inc (sqn (rt \<xi>) rip)) else None) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)).AODV()
           \<oplus> \<langle>\<xi>. dip \<xi> \<notin> vD (rt \<xi>) \<or> sqn (rt \<xi>) (dip \<xi>) < dsn \<xi> \<or> sqnf (rt \<xi>) (dip \<xi>) = unk\<rangle>
             broadcast(\<lambda>\<xi>. rreq(hops \<xi> + 1, rreqid \<xi>, dip \<xi>, max (sqn (rt \<xi>) (dip \<xi>)) (dsn \<xi>),
                                dsk \<xi>, oip \<xi>, osn \<xi>, ip \<xi>)).
             AODV()
         )
       ))"

| "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRrep = labelled PRrep (
     \<langle>\<xi>. rt \<xi> \<noteq> update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, hops \<xi> + 1, sip \<xi>) \<rangle>
     (
       \<lbrakk>\<xi>. \<xi> \<lparr> rt := update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, hops \<xi> + 1, sip \<xi>) \<rparr> \<rbrakk>
       (
         \<langle>\<xi>. oip \<xi> = ip \<xi> \<rangle>
            AODV()
         \<oplus> \<langle>\<xi>. oip \<xi> \<noteq> ip \<xi> \<rangle>
         (
           \<langle>\<xi>. oip \<xi> \<in> vD (rt \<xi>)\<rangle>
             unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (oip \<xi>)), \<lambda>\<xi>. rrep(hops \<xi> + 1, dip \<xi>,
                         dsn \<xi>, oip \<xi>, ip \<xi>)).
             AODV()
           \<triangleright>
             \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. if (rip \<in> vD (rt \<xi>) \<and> nhop (rt \<xi>) rip = nhop (rt \<xi>) (oip \<xi>))
                                     then Some (inc (sqn (rt \<xi>) rip)) else None) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
             \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
             broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)).AODV()
           \<oplus> \<langle>\<xi>. oip \<xi> \<notin> vD (rt \<xi>)\<rangle>
             AODV()
         )
       )
     )
     \<oplus> \<langle>\<xi>. rt \<xi> = update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, hops \<xi> + 1, sip \<xi>) \<rangle>
         AODV()
     )"

| "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRerr = labelled PRerr (
     \<lbrakk>\<xi>. \<xi> \<lparr> dests := (\<lambda>rip. case (dests \<xi>) rip of None \<Rightarrow> None
                       | Some rsn \<Rightarrow> if rip \<in> vD (rt \<xi>) \<and> the (nhop (rt \<xi>) rip) = sip \<xi>
                                       \<and> sqn (rt \<xi>) rip < rsn then Some rsn else None) \<rparr>\<rbrakk>
     \<lbrakk>\<xi>. \<xi> \<lparr> rt := invalidate (rt \<xi>) (dests \<xi>) \<rparr>\<rbrakk>
     \<lbrakk>\<xi>. \<xi> \<lparr> store := setRRF (store \<xi>) (dests \<xi>)\<rparr>\<rbrakk>
     (
        \<langle>\<xi>. dests \<xi> \<noteq> Map.empty\<rangle>
          broadcast(\<lambda>\<xi>. rerr(dests \<xi>, ip \<xi>)). AODV()
        \<oplus> \<langle>\<xi>. dests \<xi> = Map.empty\<rangle> 
          AODV()
     ))"



declare \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V.simps [simp del, code del]
lemmas \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_simps [simp, code] = \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V.simps [simplified]

fun \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton
where
    "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PAodv   = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PAodv)"
  | "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PNewPkt = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PNewPkt)"
  | "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PPkt    = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PPkt)"
  | "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PRreq   = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRreq)"
  | "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PRrep   = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRrep)"
  | "\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton PRerr   = seqp_skeleton (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRerr)"

lemma \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton_wf [simp]:
  "wellformed \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton pn)"
      by (cases pn) simp_all
  qed

declare \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton.simps [simp del, code del]
lemmas \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton_simps [simp, code]
           = \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_skeleton.simps [simplified \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_simps seqp_skeleton.simps]

lemma aodv_proc_cases [dest]:
  fixes p pn
  shows "p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pn) \<Longrightarrow>
                                (p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PAodv) \<or> 
                                 p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PNewPkt)  \<or>
                                 p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PPkt)  \<or>
                                 p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRreq) \<or>
                                 p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRrep) \<or>
                                 p \<in> ctermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PRerr))"
  by (cases pn) simp_all

definition \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp) set"
where "\<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i \<equiv> {(aodv_init i, \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V PAodv)}"

abbreviation paodv
  :: "ip \<Rightarrow> (state \<times> (state, msg, pseqp, pseqp label) seqp, msg seq_action) automaton"
where
  "paodv i \<equiv> \<lparr> init = \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i, trans = seqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V \<rparr>"

lemma aodv_trans: "trans (paodv i) = seqp_sos \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V"
  by simp

lemma aodv_control_within [simp]: "control_within \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (init (paodv i))"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by (rule control_withinI) (auto simp del: \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_simps)

lemma aodv_wf [simp]:
  "wellformed \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V"
  proof (rule, intro allI)
    fix pn pn'
    show "call(pn') \<notin> stermsl (\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pn)"
      by (cases pn) simp_all
  qed

lemmas aodv_labels_not_empty [simp] = labels_not_empty [OF aodv_wf]

lemma aodv_ex_label [intro]: "\<exists>l. l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
  by (metis aodv_labels_not_empty all_not_in_conv)

lemma aodv_ex_labelE [elim]:
  assumes "\<forall>l\<in>labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p. P l p"
      and "\<exists>p l. P l p \<Longrightarrow> Q"
    shows "Q"
  using assms by (metis aodv_ex_label)

lemma aodv_simple_labels [simp]: "simple_labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V"
  proof
    fix pn p
    assume "p\<in>subterms(\<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pn)"
    thus "\<exists>!l. labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p = {l}"
    by (cases pn) (simp_all cong: seqp_congs | elim disjE)+
  qed

lemma \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_labels [simp]: "(\<xi>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i \<Longrightarrow>  labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p = {PAodv-:0}"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by simp

lemma aodv_init_kD_empty [simp]:
  "(\<xi>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i \<Longrightarrow> kD (rt \<xi>) = {}"
  unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def kD_def by simp

lemma aodv_init_sip_not_ip [simp]: "\<not>(sip (aodv_init i) = i)" by simp

lemma aodv_init_sip_not_ip' [simp]:
  assumes "(\<xi>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i"
    shows "sip \<xi> \<noteq> ip \<xi>"
  using assms unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by simp

lemma aodv_init_sip_not_i [simp]:
  assumes "(\<xi>, p) \<in> \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V i"
    shows "sip \<xi> \<noteq> i"
  using assms unfolding \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def by simp

lemma clear_locals_sip_not_ip':
  assumes "ip \<xi> = i"
    shows "\<not>(sip (clear_locals \<xi>) = i)"
  using assms by auto

text \<open>Stop the simplifier from descending into process terms.\<close>
declare seqp_congs [cong]

text \<open>Configure the main invariant tactic for AODV.\<close>

declare
  \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_simps [cterms_env]
  aodv_proc_cases [ctermsl_cases]
  seq_invariant_ctermsI [OF aodv_wf aodv_control_within aodv_simple_labels aodv_trans,
                            cterms_intros]
  seq_step_invariant_ctermsI [OF aodv_wf aodv_control_within aodv_simple_labels aodv_trans,
                                 cterms_intros]

end
