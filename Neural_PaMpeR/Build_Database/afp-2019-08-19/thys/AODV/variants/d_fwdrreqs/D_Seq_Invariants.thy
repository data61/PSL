(*  Title:       variants/d_fwdrreqs/Seq_Invariants.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "Invariant proofs on individual processes"

theory D_Seq_Invariants
imports AWN.Invariants D_Aodv D_Aodv_Data D_Aodv_Predicates D_Fresher
begin

text \<open>
  The proposition numbers are taken from the December 2013 version of
  the Fehnker et al technical report.
\<close>

text \<open>Proposition 7.2\<close>

lemma sequence_number_increases:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). sn \<xi> \<le> sn \<xi>')"
  by inv_cterms

lemma sequence_number_one_or_bigger:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _). 1 \<le> sn \<xi>)"
  by (rule onll_step_to_invariantI [OF sequence_number_increases])
     (auto simp: \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def)

text \<open>We can get rid of the onl/onll if desired...\<close>

lemma sequence_number_increases':
  "paodv i \<TTurnstile>\<^sub>A (\<lambda>((\<xi>, _), _, (\<xi>', _)). sn \<xi> \<le> sn \<xi>')"
  by (rule step_invariant_weakenE [OF sequence_number_increases]) (auto dest!: onllD)

lemma sequence_number_one_or_bigger':
  "paodv i \<TTurnstile> (\<lambda>(\<xi>, _). 1 \<le> sn \<xi>)"
  by (rule invariant_weakenE [OF sequence_number_one_or_bigger]) auto

lemma sip_in_kD:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). l \<in> ({PAodv-:7} \<union> {PAodv-:5} \<union> {PRrep-:0..PRrep-:1}
                                     \<union> {PRreq-:0..PRreq-:3}) \<longrightarrow> sip \<xi> \<in> kD (rt \<xi>))"
  by inv_cterms

lemma rrep_1_update_changes:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l = PRrep-:1 \<longrightarrow>
                        rt \<xi> \<noteq> update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, hops \<xi> + 1, sip \<xi>, {})))"
  by inv_cterms

lemma addpreRT_partly_welldefined:
  "paodv i \<TTurnstile>
     onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PRreq-:18..PRreq-:20} \<union> {PRrep-:2..PRrep-:6} \<longrightarrow> dip \<xi> \<in> kD (rt \<xi>))
                      \<and> (l \<in> {PRreq-:3..PRreq-:19} \<longrightarrow> oip \<xi> \<in> kD (rt \<xi>)))"
  by inv_cterms

text \<open>Proposition 7.38\<close>

lemma includes_nhip:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). \<forall>dip\<in>kD(rt \<xi>). the (nhop (rt \<xi>) dip)\<in>kD(rt \<xi>))"
  proof -
    { fix ip and \<xi> \<xi>' :: state
      assume "\<forall>dip\<in>kD (rt \<xi>). the (nhop (rt \<xi>) dip) \<in> kD (rt \<xi>)"
         and "\<xi>' = \<xi>\<lparr>rt := update (rt \<xi>) ip (0, unk, val, Suc 0, ip, {})\<rparr>"
      hence "\<forall>dip\<in>kD (rt \<xi>).
               the (nhop (update (rt \<xi>) ip (0, unk, val, Suc 0, ip, {})) dip) = ip
             \<or> the (nhop (update (rt \<xi>) ip (0, unk, val, Suc 0, ip, {})) dip) \<in> kD (rt \<xi>)"
        by clarsimp (metis nhop_update_unk_val update_another)
    } note one_hop = this
    {  fix ip sip sn hops and \<xi> \<xi>' :: state
       assume "\<forall>dip\<in>kD (rt \<xi>). the (nhop (rt \<xi>) dip) \<in> kD (rt \<xi>)"
          and "\<xi>' = \<xi>\<lparr>rt := update (rt \<xi>) ip (sn, kno, val, Suc hops, sip, {})\<rparr>"
          and "sip \<in> kD (rt \<xi>)"
       hence "(the (nhop (update (rt \<xi>) ip (sn, kno, val, Suc hops, sip, {})) ip) = ip
                 \<or> the (nhop (update (rt \<xi>) ip (sn, kno, val, Suc hops, sip, {})) ip) \<in> kD (rt \<xi>))
               \<and> (\<forall>dip\<in>kD (rt \<xi>).
                    the (nhop (update (rt \<xi>) ip (sn, kno, val, Suc hops, sip, {})) dip) = ip
                    \<or> the (nhop (update (rt \<xi>) ip (sn, kno, val, Suc hops, sip, {})) dip) \<in> kD (rt \<xi>))"
         by (metis kD_update_unchanged nhop_update_changed update_another)
    } note nhip_is_sip = this
    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf sip_in_kD]
                              onl_invariant_sterms [OF aodv_wf addpreRT_partly_welldefined]
                       solve: one_hop nhip_is_sip)
  qed

text \<open>Proposition 7.22: needed in Proposition 7.4\<close>

lemma addpreRT_welldefined:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PRreq-:18..PRreq-:20} \<longrightarrow> dip \<xi> \<in> kD (rt \<xi>)) \<and>
                               (l = PRreq-:19 \<longrightarrow> oip \<xi> \<in> kD (rt \<xi>)) \<and>                  
                               (l = PRrep-:5  \<longrightarrow> dip \<xi> \<in> kD (rt \<xi>)) \<and>
                               (l = PRrep-:6  \<longrightarrow> (the (nhop (rt \<xi>) (dip \<xi>))) \<in> kD (rt \<xi>)))"
  (is "_ \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V ?P")
  unfolding invariant_def
  proof
    fix s
    assume "s \<in> reachable (paodv i) TT"
    then obtain \<xi> p where "s = (\<xi>, p)"
                      and "(\<xi>, p) \<in> reachable (paodv i) TT"
      by (metis prod.exhaust)
    have "onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V ?P (\<xi>, p)"
    proof (rule onlI)
      fix l
      assume "l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p"
      with \<open>(\<xi>, p) \<in> reachable (paodv i) TT\<close>
        have I1: "l \<in> {PRreq-:18..PRreq-:20} \<longrightarrow> dip \<xi> \<in> kD(rt \<xi>)"
         and I2: "l = PRreq-:19 \<longrightarrow> oip \<xi> \<in> kD(rt \<xi>)"
         and I3: "l \<in> {PRrep-:2..PRrep-:6}  \<longrightarrow> dip \<xi> \<in> kD(rt \<xi>)"
         by (auto dest!: invariantD [OF addpreRT_partly_welldefined])
      moreover from \<open>(\<xi>, p) \<in> reachable (paodv i) TT\<close> \<open>l \<in> labels \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V p\<close> and I3
        have "l = PRrep-:6  \<longrightarrow> (the (nhop (rt \<xi>) (dip \<xi>))) \<in> kD(rt \<xi>)"
          by (auto dest!: invariantD [OF includes_nhip])
      ultimately show "?P (\<xi>, l)"
        by simp
    qed
    with \<open>s = (\<xi>, p)\<close> show "onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V ?P s"
      by simp
  qed

text \<open>Proposition 7.4\<close>

lemma known_destinations_increase:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). kD (rt \<xi>) \<subseteq> kD (rt \<xi>'))"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf addpreRT_welldefined]
                 simp add: subset_insertI)

text \<open>Proposition 7.5\<close>

lemma rreqs_increase:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). rreqs \<xi> \<subseteq> rreqs \<xi>')"
  by (inv_cterms simp add: subset_insertI)

lemma dests_bigger_than_sqn:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). l \<in> {PAodv-:15..PAodv-:19}
                                 \<union> {PPkt-:7..PPkt-:11}
                                 \<union> {PRreq-:11..PRreq-:15}
                                 \<union> {PRreq-:24..PRreq-:28}
                                 \<union> {PRrep-:10..PRrep-:14}
                                 \<union> {PRerr-:1..PRerr-:5}
                         \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>kD(rt \<xi>) \<and> sqn (rt \<xi>) ip \<le> the (dests \<xi> ip)))"
  proof -
    have sqninv:
      "\<And>dests rt rsn ip.
       \<lbrakk> \<forall>ip\<in>dom(dests). ip\<in>kD(rt) \<and> sqn rt ip \<le> the (dests ip); dests ip = Some rsn \<rbrakk>
        \<Longrightarrow> sqn (invalidate rt dests) ip \<le> rsn"
        by (rule sqn_invalidate_in_dests [THEN eq_imp_le], assumption) auto
    have indests:
      "\<And>dests rt rsn ip.
       \<lbrakk> \<forall>ip\<in>dom(dests). ip\<in>kD(rt) \<and> sqn rt ip \<le> the (dests ip); dests ip = Some rsn \<rbrakk>
        \<Longrightarrow> ip\<in>kD(rt) \<and> sqn rt ip \<le> rsn"
        by (metis domI option.sel)
    show ?thesis
      by inv_cterms
         (clarsimp split: if_split_asm option.split_asm
                   elim!: sqninv indests)+
  qed

text \<open>Proposition 7.6\<close>

lemma sqns_increase:
   "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)). \<forall>ip. sqn (rt \<xi>) ip \<le> sqn (rt \<xi>') ip)"
  proof -
    { fix \<xi> :: state
      assume *: "\<forall>ip\<in>dom(dests \<xi>). ip \<in> kD (rt \<xi>) \<and> sqn (rt \<xi>) ip \<le> the (dests \<xi> ip)"
      have "\<forall>ip. sqn (rt \<xi>) ip \<le> sqn (invalidate (rt \<xi>) (dests \<xi>)) ip"
      proof
        fix ip
        from * have "ip\<notin>dom(dests \<xi>) \<or> sqn (rt \<xi>) ip \<le> the (dests \<xi> ip)" by simp
        thus "sqn (rt \<xi>) ip \<le> sqn (invalidate (rt \<xi>) (dests \<xi>)) ip"
          by (metis domI invalidate_sqn option.sel)
      qed
    } note solve_invalidate = this
    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf addpreRT_welldefined]
                              onl_invariant_sterms [OF aodv_wf dests_bigger_than_sqn]
                    simp add: solve_invalidate)
  qed

text \<open>Proposition 7.7\<close>

lemma ip_constant:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _). ip \<xi> = i)"
  by (inv_cterms simp add: \<sigma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V_def)

text \<open>Proposition 7.8\<close>

lemma sender_ip_valid':
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), a, _). anycast (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m = ip \<xi>) a)"
  by inv_cterms

lemma sender_ip_valid:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), a, _). anycast (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m = i) a)"
  by (rule step_invariant_weaken_with_invariantE [OF ip_constant sender_ip_valid'])
     (auto dest!: onlD onllD)

lemma received_msg_inv:
  "paodv i \<TTurnstile> (recvmsg P \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). l \<in> {PAodv-:1} \<longrightarrow> P (msg \<xi>))"
  by inv_cterms

text \<open>Proposition 7.9\<close>

lemma sip_not_ip':
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m \<noteq> i) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _). sip \<xi> \<noteq> ip \<xi>)"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf received_msg_inv]
                          onl_invariant_sterms [OF aodv_wf ip_constant [THEN invariant_restrict_inD]]
                simp add: clear_locals_sip_not_ip') clarsimp+

lemma sip_not_ip:
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. not_Pkt m \<longrightarrow> msg_sender m \<noteq> i) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _). sip \<xi> \<noteq> i)"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf received_msg_inv]
                          onl_invariant_sterms [OF aodv_wf ip_constant [THEN invariant_restrict_inD]]
                simp add: clear_locals_sip_not_ip') clarsimp+

text \<open>Neither \<open>sip_not_ip'\<close> nor \<open>sip_not_ip\<close> is needed to show loop freedom.\<close>

text \<open>Proposition 7.10\<close>

lemma hop_count_positive:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _). \<forall>ip\<in>kD (rt \<xi>). the (dhops (rt \<xi>) ip) \<ge> 1)"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf addpreRT_welldefined]) auto

lemma rreq_dip_in_vD_dip_eq_ip:
  "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PRreq-:18..PRreq-:21} \<longrightarrow> dip \<xi> \<in> vD(rt \<xi>))
                            \<and> (l \<in> {PRreq-:6, PRreq-:7} \<longrightarrow> dip \<xi> = ip \<xi>)
                            \<and> (l \<in> {PRreq-:17..PRreq-:21} \<longrightarrow> dip \<xi> \<noteq> ip \<xi>))"
  proof (inv_cterms, elim conjE)
    fix l \<xi> pp p'
    assume "(\<xi>, pp) \<in> reachable (paodv i) TT"
       and "{PRreq-:19}\<lbrakk>\<lambda>\<xi>. \<xi>\<lparr>rt := the (addpreRT (rt \<xi>) (oip \<xi>) {the (nhop (rt \<xi>) (dip \<xi>))})\<rparr>\<rbrakk> p'
              \<in> sterms \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pp"
       and "l = PRreq-:19"
       and "dip \<xi> \<in> vD (rt \<xi>)"
    from this(1-3) have "oip \<xi> \<in> kD (rt \<xi>)"
      by (auto dest: onl_invariant_sterms [OF aodv_wf addpreRT_welldefined, where l="PRreq-:19"])
    with \<open>dip \<xi> \<in> vD (rt \<xi>)\<close>
      show "dip \<xi> \<in> vD (the (addpreRT (rt \<xi>) (oip \<xi>) {the (nhop (rt \<xi>) (dip \<xi>))}))" by simp
  qed

text \<open>Proposition 7.11\<close>

lemma anycast_msg_zhops:
  "\<And>rreqid dip dsn dsk oip osn sip.
      paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(_, a, _). anycast msg_zhops a)"
  proof (inv_cterms inv add:
           onl_invariant_sterms [OF aodv_wf rreq_dip_in_vD_dip_eq_ip [THEN invariant_restrict_inD]]
           onl_invariant_sterms [OF aodv_wf hop_count_positive [THEN 
           invariant_restrict_inD]],
         elim conjE)
    fix l \<xi> a pp p' pp'
    assume "(\<xi>, pp) \<in> reachable (paodv i) TT"
       and "{PRreq-:20}unicast(\<lambda>\<xi>. the (nhop (rt \<xi>) (oip \<xi>)),
               \<lambda>\<xi>. Rrep (the (dhops (rt \<xi>) (dip \<xi>))) (dip \<xi>) (sqn (rt \<xi>) (dip \<xi>)) (oip \<xi>) (ip \<xi>)).
                     p' \<triangleright> pp' \<in> sterms \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pp"
       and "l = PRreq-:20"
       and "a = unicast (the (nhop (rt \<xi>) (oip \<xi>)))
                 (Rrep (the (dhops (rt \<xi>) (dip \<xi>))) (dip \<xi>) (sqn (rt \<xi>) (dip \<xi>)) (oip \<xi>) (ip \<xi>))"
       and *: "\<forall>ip\<in>kD (rt \<xi>). Suc 0 \<le> the (dhops (rt \<xi>) ip)"
       and "dip \<xi> \<in> vD (rt \<xi>)"
    from \<open>dip \<xi> \<in> vD (rt \<xi>)\<close> have "dip \<xi> \<in> kD (rt \<xi>)"
      by (rule vD_iD_gives_kD(1))
    with * have "Suc 0 \<le> the (dhops (rt \<xi>) (dip \<xi>))" ..
    thus "0 < the (dhops (rt \<xi>) (dip \<xi>))" by simp
  qed

lemma hop_count_zero_oip_dip_sip:
  "paodv i \<TTurnstile> (recvmsg msg_zhops \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                 (l\<in>{PAodv-:4..PAodv-:5} \<union> {PRreq-:n|n. True} \<longrightarrow>
                          (hops \<xi> = 0 \<longrightarrow> oip \<xi> = sip \<xi>))
                 \<and>
                 ((l\<in>{PAodv-:6..PAodv-:7} \<union> {PRrep-:n|n. True} \<longrightarrow>
                          (hops \<xi> = 0 \<longrightarrow> dip \<xi> = sip \<xi>))))"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf received_msg_inv]) auto

lemma osn_rreq:
  "paodv i \<TTurnstile> (recvmsg rreq_rrep_sn \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                                    l \<in> {PAodv-:4, PAodv-:5} \<union> {PRreq-:n|n. True} \<longrightarrow> 1 \<le> osn \<xi>)"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf received_msg_inv]) clarsimp

lemma osn_rreq':
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                                    l \<in> {PAodv-:4, PAodv-:5} \<union> {PRreq-:n|n. True} \<longrightarrow> 1 \<le> osn \<xi>)"
  proof (rule invariant_weakenE [OF osn_rreq])
    fix a
    assume "recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) a"
    thus "recvmsg rreq_rrep_sn a"
      by (cases a) simp_all
  qed

lemma dsn_rrep:
  "paodv i \<TTurnstile> (recvmsg rreq_rrep_sn \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                                    l \<in> {PAodv-:6, PAodv-:7} \<union> {PRrep-:n|n. True} \<longrightarrow> 1 \<le> dsn \<xi>)"
  by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf received_msg_inv]) clarsimp

lemma dsn_rrep':
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) \<rightarrow>)  onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                                    l \<in> {PAodv-:6, PAodv-:7} \<union> {PRrep-:n|n. True} \<longrightarrow> 1 \<le> dsn \<xi>)"
  proof (rule invariant_weakenE [OF dsn_rrep])
    fix a
    assume "recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) a"
    thus "recvmsg rreq_rrep_sn a"
      by (cases a) simp_all
  qed

lemma hop_count_zero_oip_dip_sip':
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                 (l\<in>{PAodv-:4..PAodv-:5} \<union> {PRreq-:n|n. True} \<longrightarrow>
                          (hops \<xi> = 0 \<longrightarrow> oip \<xi> = sip \<xi>))
                 \<and>
                 ((l\<in>{PAodv-:6..PAodv-:7} \<union> {PRrep-:n|n. True} \<longrightarrow>
                          (hops \<xi> = 0 \<longrightarrow> dip \<xi> = sip \<xi>))))"
  proof (rule invariant_weakenE [OF hop_count_zero_oip_dip_sip])
    fix a
    assume "recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) a"
    thus "recvmsg msg_zhops a"
      by (cases a) simp_all
  qed

text \<open>Proposition 7.12\<close>

lemma zero_seq_unk_hops_one':
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _).
                 \<forall>dip\<in>kD(rt \<xi>). (sqn (rt \<xi>) dip = 0 \<longrightarrow> sqnf (rt \<xi>) dip = unk)
                              \<and> (sqnf (rt \<xi>) dip = unk \<longrightarrow> the (dhops (rt \<xi>) dip) = 1)
                              \<and> (the (dhops (rt \<xi>) dip) = 1 \<longrightarrow> the (nhop (rt \<xi>) dip) = dip))"
  proof -
  { fix dip and \<xi> :: state and P
    assume "sqn (invalidate (rt \<xi>) (dests \<xi>)) dip = 0"
       and all: "\<forall>ip. sqn (rt \<xi>) ip \<le> sqn (invalidate (rt \<xi>) (dests \<xi>)) ip"
       and *: "sqn (rt \<xi>) dip = 0 \<Longrightarrow> P \<xi> dip"
    have "P \<xi> dip"
    proof -
      from all have "sqn (rt \<xi>) dip \<le> sqn (invalidate (rt \<xi>) (dests \<xi>)) dip" ..
      with \<open>sqn (invalidate (rt \<xi>) (dests \<xi>)) dip = 0\<close> have "sqn (rt \<xi>) dip = 0" by simp
      thus "P \<xi> dip" by (rule *)
    qed
  } note sqn_invalidate_zero [elim!] = this

  { fix dsn hops :: nat and sip oip rt and ip dip :: ip
    assume "\<forall>dip\<in>kD(rt).
                (sqn rt dip = 0 \<longrightarrow> \<pi>\<^sub>3(the (rt dip)) = unk) \<and>
                (\<pi>\<^sub>3(the (rt dip)) = unk \<longrightarrow> the (dhops rt dip) = Suc 0) \<and>
                (the (dhops rt dip) = Suc 0 \<longrightarrow> the (nhop rt dip) = dip)"
       and "hops = 0 \<longrightarrow> sip = dip"
       and "Suc 0 \<le> dsn"
       and "ip \<noteq> dip \<longrightarrow> ip\<in>kD(rt)"
    hence "the (dhops (update rt dip (dsn, kno, val, Suc hops, sip, {})) ip) = Suc 0 \<longrightarrow>
           the (nhop (update rt dip (dsn, kno, val, Suc hops, sip, {})) ip) = ip"
      by - (rule update_cases, auto simp add: sqn_def dest!: bspec)
  } note prreq_ok1 [simp] = this

  { fix ip dsn hops sip oip rt dip
    assume "\<forall>dip\<in>kD(rt).
                (sqn rt dip = 0 \<longrightarrow> \<pi>\<^sub>3(the (rt dip)) = unk) \<and>
                (\<pi>\<^sub>3(the (rt dip)) = unk \<longrightarrow> the (dhops rt dip) = Suc 0) \<and>
                (the (dhops rt dip) = Suc 0 \<longrightarrow> the (nhop rt dip) = dip)"
       and "Suc 0 \<le> dsn"
       and "ip \<noteq> dip \<longrightarrow> ip\<in>kD(rt)"
    hence "\<pi>\<^sub>3(the (update rt dip (dsn, kno, val, Suc hops, sip, {}) ip)) = unk \<longrightarrow>
           the (dhops (update rt dip (dsn, kno, val, Suc hops, sip, {})) ip) = Suc 0"
      by - (rule update_cases, auto simp add: sqn_def sqnf_def dest!: bspec)
  } note prreq_ok2 [simp] = this

  { fix ip dsn hops sip oip rt dip
    assume "\<forall>dip\<in>kD(rt).
                (sqn rt dip = 0 \<longrightarrow> \<pi>\<^sub>3(the (rt dip)) = unk) \<and>
                (\<pi>\<^sub>3(the (rt dip)) = unk \<longrightarrow> the (dhops rt dip) = Suc 0) \<and>
                (the (dhops rt dip) = Suc 0 \<longrightarrow> the (nhop rt dip) = dip)"
       and "Suc 0 \<le> dsn"
       and "ip \<noteq> dip \<longrightarrow> ip\<in>kD(rt)"
    hence "sqn (update rt dip (dsn, kno, val, Suc hops, sip, {})) ip = 0 \<longrightarrow>
           \<pi>\<^sub>3 (the (update rt dip (dsn, kno, val, Suc hops, sip, {}) ip)) = unk"
      by - (rule update_cases, auto simp add: sqn_def dest!: bspec)
  } note prreq_ok3 [simp] = this

  { fix rt sip
    assume "\<forall>dip\<in>kD rt.
              (sqn rt dip = 0 \<longrightarrow> \<pi>\<^sub>3(the (rt dip)) = unk) \<and>
              (\<pi>\<^sub>3(the (rt dip)) = unk \<longrightarrow> the (dhops rt dip) = Suc 0) \<and>
              (the (dhops rt dip) = Suc 0 \<longrightarrow> the (nhop rt dip) = dip)"
    hence "\<forall>dip\<in>kD rt.
          (sqn (update rt sip (0, unk, val, Suc 0, sip, {})) dip = 0 \<longrightarrow>
           \<pi>\<^sub>3(the (update rt sip (0, unk, val, Suc 0, sip, {}) dip)) = unk)
        \<and> (\<pi>\<^sub>3(the (update rt sip (0, unk, val, Suc 0, sip, {}) dip)) = unk \<longrightarrow>
           the (dhops (update rt sip (0, unk, val, Suc 0, sip, {})) dip) = Suc 0)
        \<and> (the (dhops (update rt sip (0, unk, val, Suc 0, sip, {})) dip) = Suc 0 \<longrightarrow>
           the (nhop (update rt sip (0, unk, val, Suc 0, sip, {})) dip) = dip)"
    by - (rule update_cases, simp_all add: sqnf_def sqn_def)
  } note prreq_ok4 [simp] = this

  have prreq_ok5 [simp]: "\<And>sip rt.
    \<pi>\<^sub>3(the (update rt sip (0, unk, val, Suc 0, sip, {}) sip)) = unk \<longrightarrow>
    the (dhops (update rt sip (0, unk, val, Suc 0, sip, {})) sip) = Suc 0"
    by (rule update_cases) simp_all

  have prreq_ok6 [simp]: "\<And>sip rt.
    sqn (update rt sip (0, unk, val, Suc 0, sip, {})) sip = 0 \<longrightarrow>
    \<pi>\<^sub>3 (the (update rt sip (0, unk, val, Suc 0, sip, {}) sip)) = unk"
    by (rule update_cases) simp_all

  show ?thesis
    by (inv_cterms inv add: onl_invariant_sterms_TT [OF aodv_wf addpreRT_welldefined]
                            onl_invariant_sterms [OF aodv_wf hop_count_zero_oip_dip_sip']
                            seq_step_invariant_sterms_TT [OF sqns_increase aodv_wf aodv_trans]
                            onl_invariant_sterms [OF aodv_wf osn_rreq']
                            onl_invariant_sterms [OF aodv_wf dsn_rrep']) clarsimp+
  qed

lemma zero_seq_unk_hops_one:
  "paodv i \<TTurnstile> (recvmsg (\<lambda>m. rreq_rrep_sn m \<and> msg_zhops m) \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, _).
                 \<forall>dip\<in>kD(rt \<xi>). (sqn (rt \<xi>) dip = 0 \<longrightarrow> (sqnf (rt \<xi>) dip = unk
                                                         \<and> the (dhops (rt \<xi>) dip) = 1
                                                         \<and> the (nhop (rt \<xi>) dip) = dip)))"
  by (rule invariant_weakenE [OF zero_seq_unk_hops_one']) auto

lemma kD_unk_or_atleast_one:
  "paodv i \<TTurnstile> (recvmsg rreq_rrep_sn \<rightarrow>) onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                               \<forall>dip\<in>kD(rt \<xi>). \<pi>\<^sub>3(the (rt \<xi> dip)) = unk \<or> 1 \<le> \<pi>\<^sub>2(the (rt \<xi> dip)))"
  proof -
    { fix sip rt dsn1 dsn2 dsk1 dsk2 flag1 flag2 hops1 hops2 nhip1 nhip2 pre1 pre2
      assume "dsk1 = unk \<or> Suc 0 \<le> dsn2"
      hence "\<pi>\<^sub>3(the (update rt sip (dsn1, dsk1, flag1, hops1, nhip1, pre1) sip)) = unk
            \<or> Suc 0 \<le> sqn (update rt sip (dsn2, dsk2, flag2, hops2, nhip2, pre2)) sip"
        unfolding update_def by (cases "dsk1 =unk") (clarsimp split: option.split)+
    } note fromsip [simp] = this

    { fix dip sip rt dsn1 dsn2 dsk1 dsk2 flag1 flag2 hops1 hops2 nhip1 nhip2 pre1 pre2
      assume allkd: "\<forall>dip\<in>kD(rt). \<pi>\<^sub>3(the (rt dip)) = unk \<or> Suc 0 \<le> sqn rt dip"
         and    **: "dsk1 = unk \<or> Suc 0 \<le> dsn2"
      have "\<forall>dip\<in>kD(rt). \<pi>\<^sub>3(the (update rt sip (dsn1, dsk1, flag1, hops1, nhip1, pre1) dip)) = unk
            \<or> Suc 0 \<le> sqn (update rt sip (dsn2, dsk2, flag2, hops2, nhip2, pre2)) dip"
        (is "\<forall>dip\<in>kD(rt). ?prop dip")
      proof
        fix dip
        assume "dip\<in>kD(rt)"
        thus "?prop dip"
        proof (cases "dip = sip")
          assume "dip = sip"
          with ** show ?thesis
            by simp
        next
          assume "dip \<noteq> sip"
          with \<open>dip\<in>kD(rt)\<close> allkd show ?thesis
            by simp
        qed
      qed
    } note solve_update [simp] = this

    { fix dip rt dests
      assume  *: "\<forall>ip\<in>dom(dests). ip\<in>kD(rt) \<and> sqn rt ip \<le> the (dests ip)"
         and **: "\<forall>ip\<in>kD(rt). \<pi>\<^sub>3(the (rt ip)) = unk \<or> Suc 0 \<le> sqn rt ip"
      have "\<forall>dip\<in>kD(rt). \<pi>\<^sub>3(the (rt dip)) = unk \<or> Suc 0 \<le> sqn (invalidate rt dests) dip"
      proof
        fix dip
        assume "dip\<in>kD(rt)"
        with ** have "\<pi>\<^sub>3(the (rt dip)) = unk \<or> Suc 0 \<le> sqn rt dip" ..
        thus "\<pi>\<^sub>3 (the (rt dip)) = unk \<or> Suc 0 \<le> sqn (invalidate rt dests) dip"
        proof
          assume "\<pi>\<^sub>3(the (rt dip)) = unk" thus ?thesis ..
        next
          assume "Suc 0 \<le> sqn rt dip"
          have "Suc 0 \<le> sqn (invalidate rt dests) dip"
          proof (cases "dip\<in>dom(dests)")
            assume "dip\<in>dom(dests)"
            with * have "sqn rt dip \<le> the (dests dip)" by simp
            with \<open>Suc 0 \<le> sqn rt dip\<close> have "Suc 0 \<le> the (dests dip)" by simp
            with \<open>dip\<in>dom(dests)\<close> \<open>dip\<in>kD(rt)\<close> [THEN kD_Some] show ?thesis
              unfolding invalidate_def sqn_def by auto
          next
            assume "dip\<notin>dom(dests)"
            with \<open>Suc 0 \<le> sqn rt dip\<close> \<open>dip\<in>kD(rt)\<close> [THEN kD_Some] show ?thesis
              unfolding invalidate_def sqn_def by auto
          qed
        thus ?thesis by (rule disjI2)
        qed
      qed
    } note solve_invalidate [simp] = this

    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms_TT [OF aodv_wf addpreRT_welldefined]
                              onl_invariant_sterms [OF aodv_wf dests_bigger_than_sqn
                                                               [THEN invariant_restrict_inD]]
                              onl_invariant_sterms [OF aodv_wf osn_rreq]
                              onl_invariant_sterms [OF aodv_wf dsn_rrep]
                    simp add: proj3_inv proj2_eq_sqn)
  qed

text \<open>Proposition 7.13\<close>

lemma rreq_rrep_sn_any_step_invariant:
  "paodv i \<TTurnstile>\<^sub>A (recvmsg rreq_rrep_sn \<rightarrow>) onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(_, a, _). anycast rreq_rrep_sn a)"
  proof -
    have sqnf_kno: "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                                      (l \<in> {PRreq-:18..PRreq-:20} \<longrightarrow> sqnf (rt \<xi>) (dip \<xi>) = kno))"
      by (inv_cterms inv add: onl_invariant_sterms_TT [OF aodv_wf addpreRT_welldefined])
    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms_TT [OF aodv_wf addpreRT_welldefined]
                              onl_invariant_sterms [OF aodv_wf sequence_number_one_or_bigger
                                                               [THEN invariant_restrict_inD]]
                              onl_invariant_sterms [OF aodv_wf kD_unk_or_atleast_one]
                              onl_invariant_sterms_TT [OF aodv_wf sqnf_kno]
                              onl_invariant_sterms [OF aodv_wf osn_rreq]
                              onl_invariant_sterms [OF aodv_wf dsn_rrep])
         (auto simp: proj2_eq_sqn)
  qed

text \<open>Proposition 7.14\<close>

lemma rreq_rrep_fresh_any_step_invariant:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), a, _). anycast (rreq_rrep_fresh (rt \<xi>)) a)"
  proof -                                                      
    have rreq_oip: "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                       (l \<in> {PRreq-:3..PRreq-:9} \<union> {PRreq-:17, PRreq-:30, PRreq-:32}
                               \<longrightarrow> oip \<xi> \<in> kD(rt \<xi>)
                                 \<and> (sqn (rt \<xi>) (oip \<xi>) > (osn \<xi>)
                                     \<or> (sqn (rt \<xi>) (oip \<xi>) = (osn \<xi>)
                                        \<and> the (dhops (rt \<xi>) (oip \<xi>)) \<le> Suc (hops \<xi>)
                                        \<and> the (flag (rt \<xi>) (oip \<xi>)) = val))))"
      proof inv_cterms
        fix l \<xi> l' pp p'
        assume "(\<xi>, pp) \<in> reachable (paodv i) TT"
           and "{PRreq-:2}\<lbrakk>\<lambda>\<xi>. \<xi>\<lparr>rt :=
                update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})\<rparr>\<rbrakk> p' \<in> sterms \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pp"
           and "l' = PRreq-:3"
        show "osn \<xi> < sqn (update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})) (oip \<xi>)
           \<or> (sqn (update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})) (oip \<xi>) = osn \<xi>
             \<and> the (dhops (update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})) (oip \<xi>))
                                                                            \<le> Suc (hops \<xi>)
             \<and> the (flag (update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})) (oip \<xi>))
                                                                            = val)"
          unfolding update_def by (clarsimp split: option.split)
                                  (metis linorder_neqE_nat not_less)
      qed

    have rrep_prrep: "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
          (l \<in> {PRrep-:2..PRrep-:7} \<longrightarrow> (dip \<xi> \<in> kD(rt \<xi>)
                                        \<and> sqn (rt \<xi>) (dip \<xi>) = dsn \<xi>
                                        \<and> the (dhops (rt \<xi>) (dip \<xi>)) = Suc (hops \<xi>)
                                        \<and> the (flag (rt \<xi>) (dip \<xi>)) = val
                                        \<and> the (nhop (rt \<xi>) (dip \<xi>)) \<in> kD (rt \<xi>))))"
      by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf rrep_1_update_changes]
                              onl_invariant_sterms [OF aodv_wf sip_in_kD])
 
    have rreq_oip_kD: "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PRreq-:3..PRreq-:28} \<longrightarrow> oip \<xi> \<in> kD(rt \<xi>)))"
      by(inv_cterms inv add: onl_invariant_sterms_TT [OF aodv_wf addpreRT_welldefined]) 

    have rreq_dip_kD_oip_sqn: "paodv i \<TTurnstile> onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l).
                       (l \<in> {PRreq-:18..PRreq-:21}
                              \<longrightarrow> (dip \<xi> \<in> kD(rt \<xi>)
                                 \<and> (sqn (rt \<xi>) (oip \<xi>) > (osn \<xi>)
                                     \<or> (sqn (rt \<xi>) (oip \<xi>) = (osn \<xi>)
                                        \<and> the (dhops (rt \<xi>) (oip \<xi>)) \<le> Suc (hops \<xi>)
                                        \<and> the (flag (rt \<xi>) (oip \<xi>)) = val)))))"
      by(inv_cterms inv add: onl_invariant_sterms [OF aodv_wf rreq_oip]
                             onl_invariant_sterms [OF aodv_wf addpreRT_welldefined])

    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf rreq_oip]
                              onl_invariant_sterms [OF aodv_wf rreq_dip_in_vD_dip_eq_ip]
                              onl_invariant_sterms [OF aodv_wf rrep_prrep]
                              onl_invariant_sterms [OF aodv_wf rreq_oip_kD]
                              onl_invariant_sterms [OF aodv_wf rreq_dip_kD_oip_sqn])
  qed

text \<open>Proposition 7.15\<close>

lemma rerr_invalid_any_step_invariant:
  "paodv i \<TTurnstile>\<^sub>A onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), a, _). anycast (rerr_invalid (rt \<xi>)) a)"
  proof -
    have dests_inv: "paodv i \<TTurnstile>
                      onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PAodv-:15, PPkt-:7, PRreq-:11,
                                            PRreq-:24, PRrep-:10, PRerr-:1}
                          \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>vD(rt \<xi>)))
                         \<and> (l \<in> {PAodv-:16..PAodv-:19}
                              \<union> {PPkt-:8..PPkt-:11}
                              \<union> {PRreq-:12..PRreq-:15}
                              \<union> {PRreq-:25..PRreq-:28}
                              \<union> {PRrep-:11..PRrep-:14}
                              \<union> {PRerr-:2..PRerr-:5} \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>iD(rt \<xi>)
                                                          \<and> the (dests \<xi> ip) = sqn (rt \<xi>) ip))
                         \<and> (l = PPkt-:14 \<longrightarrow> dip \<xi>\<in>iD(rt \<xi>)))"
      by inv_cterms (clarsimp split: if_split_asm option.split_asm simp: domIff)+
    show ?thesis
      by (inv_cterms inv add: onl_invariant_sterms [OF aodv_wf dests_inv])
  qed

text \<open>Proposition 7.16\<close>

text \<open>
  Some well-definedness obligations are irrelevant for the Isabelle development:

  \begin{enumerate}
  \item In each routing table there is at most one entry for each destination: guaranteed by type.

  \item In each store of queued data packets there is at most one data queue for
        each destination: guaranteed by structure.

  \item Whenever a set of pairs @{term "(rip, rsn)"} is assigned to the variable
        @{term "dests"} of type @{typ "ip \<rightharpoonup> sqn"}, or to the first argument of
        the function @{term "rerr"}, this set is a partial function, i.e., there
        is at most one entry @{term "(rip, rsn)"} for each destination
        @{term "rip"}: guaranteed by type.
  \end{enumerate}
\<close>

lemma dests_vD_inc_sqn:
  "paodv i \<TTurnstile>
        onl \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>(\<xi>, l). (l \<in> {PAodv-:15, PPkt-:7, PRreq-:11, PRreq-:24, PRrep-:10}
             \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>vD(rt \<xi>) \<and> the (dests \<xi> ip) = inc (sqn (rt \<xi>) ip)))
           \<and> (l = PRerr-:1
             \<longrightarrow> (\<forall>ip\<in>dom(dests \<xi>). ip\<in>vD(rt \<xi>) \<and> the (dests \<xi> ip) > sqn (rt \<xi>) ip)))"
  by inv_cterms (clarsimp split: if_split_asm option.split_asm)+

text \<open>Proposition 7.27\<close>

lemma route_tables_fresher:
  "paodv i \<TTurnstile>\<^sub>A (recvmsg rreq_rrep_sn \<rightarrow>) onll \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V (\<lambda>((\<xi>, _), _, (\<xi>', _)).
                                                                \<forall>dip\<in>kD(rt \<xi>). rt \<xi> \<sqsubseteq>\<^bsub>dip\<^esub> rt \<xi>')"
  proof (inv_cterms inv add:
           onl_invariant_sterms [OF aodv_wf dests_vD_inc_sqn [THEN invariant_restrict_inD]]
           onl_invariant_sterms [OF aodv_wf hop_count_positive [THEN invariant_restrict_inD]]
           onl_invariant_sterms [OF aodv_wf osn_rreq]
           onl_invariant_sterms [OF aodv_wf dsn_rrep]
           onl_invariant_sterms [OF aodv_wf addpreRT_welldefined [THEN invariant_restrict_inD]])
    fix \<xi> pp p'
    assume "(\<xi>, pp) \<in> reachable (paodv i) (recvmsg rreq_rrep_sn)"
       and "{PRreq-:2}\<lbrakk>\<lambda>\<xi>. \<xi>\<lparr>rt := update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})\<rparr>\<rbrakk>
               p' \<in> sterms \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pp"
       and "Suc 0 \<le> osn \<xi>"
       and *: "\<forall>ip\<in>kD (rt \<xi>). Suc 0 \<le> the (dhops (rt \<xi>) ip)"
    show "\<forall>ip\<in>kD (rt \<xi>). rt \<xi> \<sqsubseteq>\<^bsub>ip\<^esub> update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})"
    proof
      fix ip
      assume "ip\<in>kD (rt \<xi>)"
      moreover with * have "1 \<le> the (dhops (rt \<xi>) ip)" by simp
      moreover from \<open>Suc 0 \<le> osn \<xi>\<close>
        have "update_arg_wf (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})" ..
      ultimately show "rt \<xi> \<sqsubseteq>\<^bsub>ip\<^esub> update (rt \<xi>) (oip \<xi>) (osn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})"
        by (rule rt_fresher_update)
    qed
  next
    fix \<xi> pp p'
    assume "(\<xi>, pp) \<in> reachable (paodv i) (recvmsg rreq_rrep_sn)"
       and "{PRrep-:1}\<lbrakk>\<lambda>\<xi>. \<xi>\<lparr>rt := update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})\<rparr>\<rbrakk>
            p' \<in> sterms \<Gamma>\<^sub>A\<^sub>O\<^sub>D\<^sub>V pp"
       and "Suc 0 \<le> dsn \<xi>"
       and *: "\<forall>ip\<in>kD (rt \<xi>). Suc 0 \<le> the (dhops (rt \<xi>) ip)"
    show "\<forall>ip\<in>kD (rt \<xi>). rt \<xi> \<sqsubseteq>\<^bsub>ip\<^esub> update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})"
    proof
      fix ip
      assume "ip\<in>kD (rt \<xi>)"
      moreover with * have "1 \<le> the (dhops (rt \<xi>) ip)" by simp
      moreover from \<open>Suc 0 \<le> dsn \<xi>\<close>
        have "update_arg_wf (dsn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})" ..
      ultimately show "rt \<xi> \<sqsubseteq>\<^bsub>ip\<^esub> update (rt \<xi>) (dip \<xi>) (dsn \<xi>, kno, val, Suc (hops \<xi>), sip \<xi>, {})"
        by (rule rt_fresher_update)
    qed
  qed

end

