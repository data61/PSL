(*  Title:       variants/a_norreqid/Aodv_Predicates.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "Invariant assumptions and properties"

theory A_Aodv_Predicates
imports A_Aodv
begin

text \<open>Definitions for expression assumptions on incoming messages and properties of
      outgoing messages.\<close>

abbreviation not_Pkt :: "msg \<Rightarrow> bool"
where "not_Pkt m \<equiv> case m of Pkt _ _ _ \<Rightarrow> False | _ \<Rightarrow> True"

definition msg_sender :: "msg \<Rightarrow> ip"
where "msg_sender m \<equiv> case m of Rreq _ _ _ _ _ _ ipc \<Rightarrow> ipc
                              | Rrep _ _ _ _ ipc \<Rightarrow> ipc
                              | Rerr _ ipc \<Rightarrow> ipc
                              | Pkt _ _ ipc \<Rightarrow> ipc"

lemma msg_sender_simps [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
                          msg_sender (Rreq hops dip dsn dsk oip osn sip) = sip"
  "\<And>hops dip dsn oip sip. msg_sender (Rrep hops dip dsn oip sip) = sip"
  "\<And>dests sip.            msg_sender (Rerr dests sip) = sip"
  "\<And>d dip sip.            msg_sender (Pkt d dip sip) = sip"
  unfolding msg_sender_def by simp_all

definition msg_zhops :: "msg \<Rightarrow> bool"
where "msg_zhops m \<equiv> case m of
                                 Rreq hopsc dipc _ _ oipc _ sipc \<Rightarrow> hopsc = 0 \<longrightarrow> oipc = sipc
                               | Rrep hopsc dipc _ _ sipc \<Rightarrow> hopsc = 0 \<longrightarrow> dipc = sipc
                               | _ \<Rightarrow> True"

lemma msg_zhops_simps [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
           msg_zhops (Rreq hops dip dsn dsk oip osn sip) = (hops = 0 \<longrightarrow> oip = sip)"
  "\<And>hops dip dsn oip sip. msg_zhops (Rrep hops dip dsn oip sip) = (hops = 0 \<longrightarrow> dip = sip)"
  "\<And>dests sip.            msg_zhops (Rerr dests sip)        = True"
  "\<And>d dip.                msg_zhops (Newpkt d dip)          = True"
  "\<And>d dip sip.            msg_zhops (Pkt d dip sip)         = True"
  unfolding msg_zhops_def by simp_all

definition rreq_rrep_sn :: "msg \<Rightarrow> bool"
where "rreq_rrep_sn m \<equiv> case m of Rreq  _ _ _ _ _ osnc _ \<Rightarrow> osnc \<ge> 1
                                | Rrep _ _ dsnc _ _ \<Rightarrow> dsnc \<ge> 1
                                | _ \<Rightarrow> True"

lemma rreq_rrep_sn_simps [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
           rreq_rrep_sn (Rreq hops dip dsn dsk oip osn sip) = (osn \<ge> 1)"
  "\<And>hops dip dsn oip sip. rreq_rrep_sn (Rrep hops dip dsn oip sip) = (dsn \<ge> 1)"
  "\<And>dests sip.            rreq_rrep_sn (Rerr dests sip) = True"
  "\<And>d dip.                rreq_rrep_sn (Newpkt d dip)   = True"
  "\<And>d dip sip.            rreq_rrep_sn (Pkt d dip sip)  = True"
  unfolding rreq_rrep_sn_def by simp_all

definition rreq_rrep_fresh :: "rt \<Rightarrow> msg \<Rightarrow> bool"
where "rreq_rrep_fresh crt m \<equiv> case m of Rreq hopsc  _ _ _ oipc osnc ipcc \<Rightarrow> (ipcc \<noteq> oipc \<longrightarrow>
                                                oipc\<in>kD(crt) \<and> (sqn crt oipc > osnc
                                                                \<or> (sqn crt oipc = osnc
                                                                   \<and> the (dhops crt oipc) \<le> hopsc
                                                                   \<and> the (flag crt oipc) = val)))
                                | Rrep hopsc dipc dsnc _ ipcc \<Rightarrow> (ipcc \<noteq> dipc \<longrightarrow> 
                                                                    dipc\<in>kD(crt)
                                                                  \<and> sqn crt dipc = dsnc
                                                                  \<and> the (dhops crt dipc) = hopsc
                                                                  \<and> the (flag crt dipc) = val)
                                | _ \<Rightarrow> True"

lemma rreq_rrep_fresh [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
           rreq_rrep_fresh crt (Rreq hops dip dsn dsk oip osn sip) =
                               (sip \<noteq> oip \<longrightarrow> oip\<in>kD(crt)
                                            \<and> (sqn crt oip > osn
                                               \<or> (sqn crt oip = osn
                                                  \<and> the (dhops crt oip) \<le> hops
                                                  \<and> the (flag crt oip) = val)))"
  "\<And>hops dip dsn oip sip. rreq_rrep_fresh crt (Rrep hops dip dsn oip sip) =
                               (sip \<noteq> dip \<longrightarrow> dip\<in>kD(crt)
                                              \<and> sqn crt dip = dsn
                                              \<and> the (dhops crt dip) = hops
                                              \<and> the (flag crt dip) = val)"
  "\<And>dests sip.            rreq_rrep_fresh crt (Rerr dests sip) = True"
  "\<And>d dip.                rreq_rrep_fresh crt (Newpkt d dip)   = True"
  "\<And>d dip sip.            rreq_rrep_fresh crt (Pkt d dip sip)  = True"
  unfolding rreq_rrep_fresh_def by simp_all

definition rerr_invalid :: "rt \<Rightarrow> msg \<Rightarrow> bool"
where "rerr_invalid crt m \<equiv> case m of Rerr destsc _ \<Rightarrow> (\<forall>ripc\<in>dom(destsc).
                                            (ripc\<in>iD(crt) \<and> the (destsc ripc) = sqn crt ripc))
                                | _ \<Rightarrow> True"

lemma rerr_invalid [simp]:
  "\<And>hops dip dsn dsk oip osn sip.
                           rerr_invalid crt (Rreq hops dip dsn dsk oip osn sip) = True"
  "\<And>hops dip dsn oip sip. rerr_invalid crt (Rrep hops dip dsn oip sip) = True"
  "\<And>dests sip.            rerr_invalid crt (Rerr dests sip) = (\<forall>rip\<in>dom(dests).
                                                 rip\<in>iD(crt) \<and> the (dests rip) = sqn crt rip)"
  "\<And>d dip.                rerr_invalid crt (Newpkt d dip)   = True"
  "\<And>d dip sip.            rerr_invalid crt (Pkt d dip sip)  = True"
  unfolding rerr_invalid_def by simp_all

definition
  initmissing :: "(nat \<Rightarrow> state option) \<times> 'a \<Rightarrow> (nat \<Rightarrow> state) \<times> 'a"
where
  "initmissing \<sigma> = (\<lambda>i. case (fst \<sigma>) i of None \<Rightarrow> aodv_init i | Some s \<Rightarrow> s, snd \<sigma>)"

lemma not_in_net_ips_fst_init_missing [simp]:
  assumes "i \<notin> net_ips \<sigma>"
    shows "fst (initmissing (netgmap fst \<sigma>)) i = aodv_init i"
  using assms unfolding initmissing_def by simp

lemma fst_initmissing_netgmap_pair_fst [simp]:
  "fst (initmissing (netgmap (\<lambda>(p, q). (fst (id p), snd (id p), q)) s))
                                               = fst (initmissing (netgmap fst s))"
  unfolding initmissing_def by auto

text \<open>We introduce a streamlined alternative to @{term initmissing} with @{term netgmap}
        to simplify invariant statements and thus facilitate their comprehension and
        presentation.\<close>

lemma fst_initmissing_netgmap_default_aodv_init_netlift:
  "fst (initmissing (netgmap fst s)) = default aodv_init (netlift fst s)"
  unfolding initmissing_def default_def
  by (simp add: fst_netgmap_netlift del: One_nat_def)

definition
  netglobal :: "((nat \<Rightarrow> state) \<Rightarrow> bool) \<Rightarrow> ((state \<times> 'b) \<times> 'c) net_state \<Rightarrow> bool"
where
  "netglobal P \<equiv> (\<lambda>s. P (default aodv_init (netlift fst s)))"

end
