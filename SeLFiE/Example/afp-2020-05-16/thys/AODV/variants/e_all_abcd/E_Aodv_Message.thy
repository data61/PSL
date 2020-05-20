(*  Title:       variants/e_all_abcd/Aodv_Message.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "AODV protocol messages"

theory E_Aodv_Message
imports E_All_ABCD
begin

datatype msg =
    Rreq nat ip sqn k ip sqn ip bool
  | Rrep nat ip sqn ip ip
  | Rerr "ip \<rightharpoonup> sqn" ip
  | Newpkt data ip
  | Pkt data ip ip

instantiation msg :: msg
begin
  definition newpkt_def [simp]: "newpkt \<equiv> \<lambda>(d, dip). Newpkt d dip"
  definition eq_newpkt_def: "eq_newpkt m \<equiv> case m of Newpkt d dip \<Rightarrow> True | _ \<Rightarrow> False"

  instance by intro_classes (simp add: eq_newpkt_def)
end

text \<open>The @{type msg} type models the different messages used within AODV.
      The instantiation as a @{class msg} is a technicality due to the special
      treatment of @{term newpkt} messages in the AWN SOS rules.
      This use of classes allows a clean separation of the AWN-specific definitions
      and these AODV-specific definitions.\<close>

definition rreq :: "nat \<times> ip \<times> sqn \<times> k \<times> ip \<times> sqn \<times> ip \<times> bool \<Rightarrow> msg"
  where "rreq \<equiv> \<lambda>(hops, dip, dsn, dsk, oip, osn, sip, handled).
                    Rreq hops dip dsn dsk oip osn sip handled"

lemma rreq_simp [simp]:
  "rreq(hops, dip, dsn, dsk, oip, osn, sip, handled) =  Rreq hops dip dsn dsk oip osn sip handled"
  unfolding rreq_def by simp

definition rrep :: "nat \<times> ip \<times> sqn \<times> ip \<times> ip \<Rightarrow> msg"
  where "rrep \<equiv> \<lambda>(hops, dip, dsn, oip, sip). Rrep hops dip dsn oip sip"

lemma rrep_simp [simp]:
  "rrep(hops, dip, dsn, oip, sip) = Rrep hops dip dsn oip sip"
  unfolding rrep_def by simp

definition rerr :: "(ip \<rightharpoonup> sqn) \<times> ip \<Rightarrow> msg"
  where "rerr \<equiv> \<lambda>(dests, sip). Rerr dests sip"

lemma rerr_simp [simp]:
  "rerr(dests, sip) = Rerr dests sip"
  unfolding rerr_def by simp

lemma not_eq_newpkt_rreq [simp]: "\<not>eq_newpkt (Rreq hops dip dsn dsk oip osn sip handled)"
  unfolding eq_newpkt_def by simp

lemma not_eq_newpkt_rrep [simp]: "\<not>eq_newpkt (Rrep hops dip dsn oip sip)"
  unfolding eq_newpkt_def by simp

lemma not_eq_newpkt_rerr [simp]: "\<not>eq_newpkt (Rerr dests sip)"
  unfolding eq_newpkt_def by simp

lemma not_eq_newpkt_pkt [simp]: "\<not>eq_newpkt (Pkt d dip sip)"
  unfolding eq_newpkt_def by simp

definition pkt :: "data \<times> ip \<times> ip \<Rightarrow> msg"
  where "pkt \<equiv> \<lambda>(d, dip, sip). Pkt d dip sip"

lemma pkt_simp [simp]:
  "pkt(d, dip, sip) = Pkt d dip sip"
  unfolding pkt_def by simp

end
