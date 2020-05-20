(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  pfslvl2.thy (Isabelle/HOL 2016-1)
  ID:      $Id: pfslvl2.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-2 protocol using ephemeral asymmetric keys to achieve forward secrecy.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Key Transport Protocol with PFS (L2)\<close>

theory pfslvl2
imports pfslvl1 Channels
begin

declare domIff [simp, iff del]

(**************************************************************************************************)
subsection \<open>State and Events\<close>
(**************************************************************************************************)

text \<open>initial compromise\<close>

consts
  bad_init :: "agent set" 

specification (bad_init)
  bad_init_spec: "test_owner \<notin> bad_init \<and> test_partner \<notin> bad_init"
by auto



text \<open>level 2 state\<close>
record l2_state = 
  l1_state +
  chan :: "chan set"
  bad :: "agent set"


type_synonym l2_obs = "l2_state"

type_synonym
  l2_pred = "l2_state set"

type_synonym
  l2_trans = "(l2_state \<times> l2_state) set"



text \<open>attacker events\<close>
definition
  l2_dy_fake_msg :: "msg \<Rightarrow> l2_trans"
where
  "l2_dy_fake_msg m \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    m \<in> dy_fake_msg (bad s) (ik s) (chan s) \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>ik := {m} \<union> ik s\<rparr>
  }"

definition
  l2_dy_fake_chan :: "chan \<Rightarrow> l2_trans"
where
  "l2_dy_fake_chan M \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    M \<in> dy_fake_chan (bad s) (ik s) (chan s)\<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>chan := {M} \<union> chan s\<rparr>
  }"


text \<open>partnering\<close>
fun
  role_comp :: "role_t \<Rightarrow> role_t"
where
  "role_comp Init = Resp"
| "role_comp Resp = Init"

definition
  matching :: "frame \<Rightarrow> frame \<Rightarrow> bool"
where
  "matching sigma sigma' \<equiv> \<forall> x. x \<in> dom sigma \<inter> dom sigma' \<longrightarrow> sigma x = sigma' x"

definition
  partner_runs :: "rid_t \<Rightarrow> rid_t \<Rightarrow> bool"
where
  "partner_runs R R' \<equiv> 
    role (guessed_runs R) = role_comp (role (guessed_runs R')) \<and>
    owner (guessed_runs R) = partner (guessed_runs R') \<and>
    owner (guessed_runs R') = partner (guessed_runs R) \<and>
    matching (guessed_frame R) (guessed_frame R')
  "

lemma role_comp_inv [simp]:
  "role_comp (role_comp x) = x"
by (cases x, auto)

lemma role_comp_inv_eq:
  "y = role_comp x \<longleftrightarrow> x = role_comp y"
by (auto elim!: role_comp.elims [OF sym])

definition
  partners :: "rid_t set"
where
  "partners \<equiv> {R. partner_runs test R}"

lemma test_not_partner [simp]:
  "test \<notin> partners"
by (auto simp add: partners_def partner_runs_def, cases "role (guessed_runs test)", auto)


lemma matching_symmetric:
  "matching sigma sigma' \<Longrightarrow> matching sigma' sigma"
by (auto simp add: matching_def)

lemma partner_symmetric:
  "partner_runs R R' \<Longrightarrow> partner_runs R' R"
by (auto simp add: partner_runs_def matching_symmetric)

lemma partner_unique:
  "partner_runs R R'' \<Longrightarrow> partner_runs R R' \<Longrightarrow> R' = R''"
proof -
  assume H':"partner_runs R R'"
  then have Hm': "matching (guessed_frame R) (guessed_frame R')"
    by (auto simp add: partner_runs_def)
  assume H'':"partner_runs R R''"
  then have Hm'': "matching (guessed_frame R) (guessed_frame R'')"
    by (auto simp add: partner_runs_def)
  show ?thesis
    proof (cases "role (guessed_runs R')")
      case Init
      with H' partner_symmetric [OF H''] have Hrole:"role (guessed_runs R) = Resp"
                                                    "role (guessed_runs R'') = Init"
        by (auto simp add: partner_runs_def)
      with Init Hm' have "guessed_frame R xpkE = Some (epubKF (R'$kE))"
        by (simp add: matching_def)
      moreover from Hrole Hm'' have "guessed_frame R xpkE = Some (epubKF (R''$kE))"
        by (simp add: matching_def)
      ultimately show ?thesis by simp
    next
      case Resp
      with H' partner_symmetric [OF H''] have Hrole:"role (guessed_runs R) = Init"
                                                    "role (guessed_runs R'') = Resp"
        by (auto simp add: partner_runs_def)
      with Resp Hm' have "guessed_frame R xsk = Some (NonceF (R'$sk))"
        by (simp add: matching_def)
      moreover from Hrole Hm'' have "guessed_frame R xsk = Some (NonceF (R''$sk))"
        by (simp add: matching_def)
      ultimately show ?thesis by simp
    qed
qed

lemma partner_test:
  "R \<in> partners \<Longrightarrow> partner_runs R R' \<Longrightarrow> R' = test"
by (auto intro!:partner_unique simp add:partners_def partner_symmetric)

text \<open>compromising events\<close>
definition
  l2_lkr_others :: "agent \<Rightarrow> l2_trans"
where
  "l2_lkr_others A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    A \<noteq> test_owner \<and>
    A \<noteq> test_partner \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s\<rparr>
  }"

definition
  l2_lkr_actor :: "agent \<Rightarrow> l2_trans"
where
  "l2_lkr_actor A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    A = test_owner \<and>
    A \<noteq> test_partner \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s\<rparr>
  }"

definition
  l2_lkr_after :: "agent \<Rightarrow> l2_trans"
where
  "l2_lkr_after A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    test_ended s \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s\<rparr>
  }"

definition
  l2_skr :: "rid_t \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_skr R K \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    R \<noteq> test \<and> R \<notin> partners \<and>
    in_progress (progress s R) xsk \<and>
    guessed_frame R xsk = Some K \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>ik := {K} \<union> ik s\<rparr>
  }"


text \<open>protocol events\<close>
definition
    l2_step1 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> l2_trans"
where
  "l2_step1 Ra A B \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (progress s) \<and>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      progress := (progress s)(Ra \<mapsto> {xpkE, xskE}),
      chan := {Auth A B (\<langle>Number 0, epubKF (Ra$kE)\<rangle>)} \<union> (chan s)
      \<rparr>
  }"

definition
  l2_step2 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step2 Rb A B KE \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    Rb \<notin> dom (progress s) \<and>
    guessed_frame Rb xpkE = Some KE \<and>
    Auth A B \<langle>Number 0, KE\<rangle> \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      progress := (progress s)(Rb \<mapsto> {xpkE, xsk}),
      chan := {Auth B A (Aenc (NonceF (Rb$sk)) KE)} \<union> (chan s),
      signals := if can_signal s A B then
                   addSignal (signals s) (Running A B \<langle>KE, NonceF (Rb$sk)\<rangle>)
                 else
                   signals s,
      secret := {x. x = NonceF (Rb$sk) \<and> Rb = test} \<union> secret s
         \<rparr>
  }"  


definition
  l2_step3 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step3 Ra A B K \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    progress s Ra = Some {xpkE, xskE} \<and>
    guessed_frame Ra xsk = Some K \<and>
    Auth B A (Aenc K (epubKF (Ra$kE))) \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Ra \<mapsto> {xpkE, xskE, xsk}),
            signals := if can_signal s A B then
                         addSignal (signals s) (Commit A B \<langle>epubKF (Ra$kE),K\<rangle>)
                       else
                         signals s,
            secret := {x. x = K \<and> Ra = test} \<union> secret s
          \<rparr>
  }"


text \<open>specification\<close>
definition 
  l2_init :: "l2_state set"
where
  "l2_init \<equiv> { \<lparr>
    ik = {},
    secret = {},
    progress = Map.empty,
    signals = \<lambda>x. 0,
    chan = {},
    bad = bad_init
    \<rparr>}"

definition 
  l2_trans :: "l2_trans" where
  "l2_trans \<equiv> (\<Union>m M KE Rb Ra A B K.
     l2_step1 Ra A B \<union>
     l2_step2 Rb A B KE \<union>
     l2_step3 Ra A B m \<union>
     l2_dy_fake_chan M \<union>
     l2_dy_fake_msg m \<union>
     l2_lkr_others A \<union>
     l2_lkr_after A \<union>
     l2_skr Ra K \<union>
     Id
  )"


definition 
  l2 :: "(l2_state, l2_obs) spec" where
  "l2 \<equiv> \<lparr>
    init = l2_init,
    trans = l2_trans,
    obs = id
  \<rparr>"

lemmas l2_loc_defs = 
  l2_step1_def l2_step2_def l2_step3_def
  l2_def l2_init_def l2_trans_def
  l2_dy_fake_chan_def l2_dy_fake_msg_def
  l2_lkr_after_def l2_lkr_others_def l2_skr_def

lemmas l2_defs = l2_loc_defs ik_dy_def

lemmas l2_nostep_defs = l2_def l2_init_def l2_trans_def


lemma l2_obs_id [simp]: "obs l2 = id"
by (simp add: l2_def)


text \<open>Once a run is finished, it stays finished, therefore if the test is not finished at some
point then it was not finished before either\<close>
declare domIff [iff]
lemma l2_run_ended_trans:
  "run_ended (progress s R) \<Longrightarrow>
   (s, s') \<in> trans l2 \<Longrightarrow>
   run_ended (progress s' R)"
apply (auto simp add: l2_nostep_defs)
apply (simp add: l2_defs, fast ?)+
done
declare domIff [iff del]

lemma l2_can_signal_trans:
  "can_signal s' A B \<Longrightarrow>
  (s, s') \<in> trans l2 \<Longrightarrow>
  can_signal s A B"
by (auto simp add: can_signal_def l2_run_ended_trans)


(**************************************************************************************************)
subsection \<open>Invariants\<close>
(**************************************************************************************************)

subsubsection \<open>inv1\<close>
(**************************************************************************************************)

text \<open>If @{term "can_signal s A B"} (i.e., @{term "A"}, @{term "B"} are the test session 
agents and the test is not finished), then @{term "A"}, @{term "B"} are honest.\<close>

definition
  l2_inv1 :: "l2_state set"
where
  "l2_inv1 \<equiv> {s. \<forall>A B.
    can_signal s A B \<longrightarrow>
    A \<notin> bad s \<and> B \<notin> bad s
  }"

lemmas l2_inv1I = l2_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv1E [elim] = l2_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv1D = l2_inv1_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv1_init [iff]:
  "init l2 \<subseteq> l2_inv1"
by (auto simp add: l2_def l2_init_def l2_inv1_def can_signal_def bad_init_spec)

lemma l2_inv1_trans [iff]:
  "{l2_inv1} trans l2 {> l2_inv1}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv1I  del: conjI)
  fix s' s :: l2_state
  fix A B
  assume HI:"s \<in> l2_inv1"  
  assume HT:"(s, s') \<in> trans l2"
  assume "can_signal s' A B"
  with HT have HS:"can_signal s A B"
    by (auto simp add: l2_can_signal_trans)
  with HI have "A \<notin> bad s \<and> B \<notin> bad s"
    by fast
  with HS HT show "A \<notin> bad s' \<and> B \<notin> bad s'"
    by (auto simp add: l2_nostep_defs can_signal_def)
       (simp_all add: l2_defs)
qed

lemma PO_l2_inv1 [iff]: "reach l2 \<subseteq> l2_inv1"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv2 (authentication guard)\<close>
(**************************************************************************************************)

text \<open>
  If @{term "Auth A B (\<langle>Number 0, KE\<rangle>) \<in> chan s"} and @{term "A"}, @{term "B"} are honest
  then the message has indeed been sent by an initiator run (with the right agents etc.)\<close>

definition
  l2_inv2 :: "l2_state set"
where
  "l2_inv2 \<equiv> {s. \<forall> A B KE.
    Auth A B \<langle>Number 0, KE\<rangle> \<in> chan s \<longrightarrow>
    A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
    (\<exists> Ra.
      guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
      in_progress (progress s Ra) xpkE \<and>
      KE = epubKF (Ra$kE))
  }"

lemmas l2_inv2I = l2_inv2_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv2E [elim] = l2_inv2_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv2D = l2_inv2_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv2_init [iff]:
  "init l2 \<subseteq> l2_inv2"
by (auto simp add: l2_def l2_init_def l2_inv2_def)

lemma l2_inv2_trans [iff]:
  "{l2_inv2} trans l2 {> l2_inv2}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv2I)
apply (auto simp add: l2_defs dy_fake_chan_def)
apply force+
done

lemma PO_l2_inv2 [iff]: "reach l2 \<subseteq> l2_inv2"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv3 (authentication guard)\<close>
(**************************************************************************************************)

text \<open>If @{term "Auth B A (Aenc K (epubKF (Ra $ kE))) \<in> chan s"}
 and @{term "A"}, @{term "B"} are honest then the message has indeed been sent by a
 responder run (etc).\<close>

definition
  l2_inv3 :: "l2_state set"
where
  "l2_inv3 \<equiv> {s. \<forall> Ra A B K.
     Auth B A (Aenc K (epubKF (Ra $ kE))) \<in> chan s \<longrightarrow>
     A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
     (\<exists> Rb.
       guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
       progress s Rb = Some {xpkE, xsk} \<and>
       guessed_frame Rb xpkE = Some (epubKF (Ra$kE))\<and>
       K = NonceF (Rb$sk)
     )
    }"

lemmas l2_inv3I = l2_inv3_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv3E [elim] = l2_inv3_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv3D = l2_inv3_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv3_init [iff]:
  "init l2 \<subseteq> l2_inv3"
by (auto simp add: l2_def l2_init_def l2_inv3_def)

lemma l2_inv3_trans [iff]:
  "{l2_inv3} trans l2 {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv3I)
apply (auto simp add: l2_defs dy_fake_chan_def)
apply (simp_all add: domIff)
apply force+
done

lemma PO_l2_inv3 [iff]: "reach l2 \<subseteq> l2_inv3"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv4\<close>
(**************************************************************************************************)

text \<open>If the test run is finished and has the session key generated by a run,
  then this run is also finished.\<close>

definition
  l2_inv4 :: "l2_state set"
where
  "l2_inv4 \<equiv> {s. \<forall>Rb.
    in_progress (progress s test) xsk \<longrightarrow>
    guessed_frame test xsk = Some (NonceF (Rb$sk)) \<longrightarrow>
    progress s Rb = Some {xpkE, xsk}
  }"

lemmas l2_inv4I = l2_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv4E [elim] = l2_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv4D = l2_inv4_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv4_init [iff]:
  "init l2 \<subseteq> l2_inv4"
by (auto simp add: l2_def l2_init_def l2_inv4_def)

lemma l2_inv4_trans [iff]:
  "{l2_inv4 \<inter> l2_inv3 \<inter> l2_inv1} trans l2 {> l2_inv4}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv4I)
apply (auto simp add: l2_defs dy_fake_chan_def)
apply (auto dest!: l2_inv4D simp add: domIff can_signal_def)
apply (auto dest!: l2_inv3D intro!:l2_inv1D simp add: can_signal_def)
done

lemma PO_l2_inv4 [iff]: "reach l2 \<subseteq> l2_inv4"
by (rule_tac J="l2_inv3 \<inter> l2_inv1" in inv_rule_incr) (auto)


subsubsection \<open>inv5\<close>
(**************************************************************************************************)

text \<open>The only confidential or secure messages on the channel have been put there
  by the attacker.\<close>

definition
  l2_inv5 :: "l2_state set"
where
  "l2_inv5 \<equiv> {s. \<forall>A B M.
    (Confid A B M \<in> chan s \<or> Secure A B M \<in> chan s) \<longrightarrow> 
    M \<in> dy_fake_msg (bad s) (ik s) (chan s)
  }"

lemmas l2_inv5I = l2_inv5_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv5E [elim] = l2_inv5_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv5D = l2_inv5_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv5_init [iff]:
  "init l2 \<subseteq> l2_inv5"
by (auto simp add: l2_def l2_init_def l2_inv5_def)

lemma l2_inv5_trans [iff]:
  "{l2_inv5} trans l2 {> l2_inv5}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv5I)
apply (auto simp add: l2_defs dy_fake_chan_def intro: l2_inv5D dy_fake_msg_monotone)
done

lemma PO_l2_inv5 [iff]: "reach l2 \<subseteq> l2_inv5"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv6\<close>
(**************************************************************************************************)

text \<open>If an initiator @{term "Ra"} knows a session key @{term "K"}, then the attacker
  knows @{term "Aenc K (epubKF (Ra$kE))"}.\<close>

definition
  l2_inv6 :: "l2_state set"
where
  "l2_inv6 \<equiv> {s. \<forall>Ra K.
    role (guessed_runs Ra) = Init \<longrightarrow>
    in_progress (progress s Ra) xsk \<longrightarrow>
    guessed_frame Ra xsk = Some K \<longrightarrow>
    Aenc K (epubKF (Ra$kE)) \<in> extr (bad s) (ik s) (chan s)
  }"

lemmas l2_inv6I = l2_inv6_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv6E [elim] = l2_inv6_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv6D = l2_inv6_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv6_init [iff]:
  "init l2 \<subseteq> l2_inv6"
by (auto simp add: l2_def l2_init_def l2_inv6_def)

lemma l2_inv6_trans [iff]:
  "{l2_inv6} trans l2 {> l2_inv6}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv6I)
apply (auto simp add: l2_defs dy_fake_chan_def dest: l2_inv6D)
done

lemma PO_l2_inv6 [iff]: "reach l2 \<subseteq> l2_inv6"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv7\<close>
(**************************************************************************************************)

text \<open>Form of the messages in @{term "extr (bad s) (ik s) (chan s)"} =
  @{term "synth (analz (generators))"}.\<close>

abbreviation
  "generators \<equiv> range epubK \<union>
         {Aenc (NonceF (Rb $ sk)) (epubKF (Ra$kE)) |Ra Rb. \<exists> A B.
            guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
            guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
            guessed_frame Rb xpkE = Some (epubKF (Ra$kE))} \<union>
         {NonceF (R $ sk) |R. R \<noteq> test \<and> R \<notin> partners}"

lemma analz_generators: "analz generators = generators"
by (rule, rule, erule analz.induct, auto)

definition
  l2_inv7 :: "l2_state set"
where
  "l2_inv7 \<equiv> {s. 
    extr (bad s) (ik s) (chan s) \<subseteq> 
      synth (analz (generators))
  }"

lemmas l2_inv7I = l2_inv7_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv7E [elim] = l2_inv7_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv7D = l2_inv7_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv7_init [iff]:
  "init l2 \<subseteq> l2_inv7"
by (auto simp add: l2_def l2_init_def l2_inv7_def)

lemma l2_inv7_step1:
  "{l2_inv7} l2_step1 Ra A B {> l2_inv7}"
apply (auto simp add: PO_hoare_defs l2_defs intro!: l2_inv7I)
apply (auto dest: l2_inv7D [THEN [2] rev_subsetD])+
done

lemma l2_inv7_step2:
  "{l2_inv1 \<inter> l2_inv2 \<inter> l2_inv4 \<inter> l2_inv7} l2_step2 Rb A B KE {> l2_inv7}"
proof (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv7I)
  fix s' s :: l2_state
  fix x
  assume Hx:"x \<in> extr (bad s') (ik s') (chan s')"
  assume Hi:"s \<in> l2_inv7"
  assume Hi':"s \<in> l2_inv1"
  assume Hi'':"s \<in> l2_inv2"
  assume Hi''':"s \<in> l2_inv4"
  assume Hs:"(s, s') \<in> l2_step2 Rb A B KE"
  from Hx Hi Hs show " x \<in> synth (analz (generators))"
    proof (auto simp add: l2_defs dest: l2_inv7D [THEN [2] rev_subsetD])
      txt \<open>first case: @{term "can_signal s A B"}, which implies that @{term "A"}, @{term "B"} are
      honest, and therefore the public key received by @{term "B"} is not from the attacker,
      which proves that the
      message added to the channel is in @{term "{z. \<exists>x k. z = Aenc x (epubKF k)}"}\<close>
      assume Hc:"Auth A B \<langle>Number 0, KE\<rangle> \<in> chan s"
      assume HRb:"guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
                 "guessed_frame Rb xpkE = Some KE"
      assume Hcs: "can_signal s A B"
      from Hcs Hi' have "A \<notin> bad s \<and> B \<notin> bad s"
        by auto
      with Hc Hi'' obtain Ra where "KE = epubKF (Ra$kE)" 
                             and "guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
        by (auto dest: l2_inv2D)
      with HRb show "Aenc (NonceF (Rb $ sk)) KE \<in> synth (analz generators)"
        by blast
    next
      txt \<open>second case: @{term "\<not> can_signal s A B"}. We show that @{term "Rb"} is not test and
        not a partner:
      - @{term "Rb"} is not test because in that case test is not finished and
        @{term "A"}, @{term "B"} are the test agents, thus
        @{term "can_signal s A B"}
      - @{term "Rb"} is not a partner for the same reason
      therefore the message added to the channel can be constructed from
      @{term "{NonceF (R $ sk) |R. R \<noteq> test \<and> R \<notin> partners}"}\<close>
      assume Hc:"Auth A B \<langle>Number 0, KE\<rangle> \<in> chan s"
      assume Hcs:"\<not> can_signal s A B"
      assume HRb:"Rb \<notin> dom (progress s)"
                  "guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
      from Hcs HRb have "Rb \<noteq> test"
        by (auto simp add: can_signal_def domIff)
      moreover from HRb Hi''' Hcs have "Rb \<notin> partners"
        by (clarify, auto simp add: partners_def partner_runs_def can_signal_def matching_def domIff)
      moreover from Hc Hi have "KE \<in> synth (analz (generators))"
        by auto
      ultimately show "Aenc (NonceF (Rb $ sk)) KE \<in> synth (analz (generators))"
        by blast
    qed    
qed

lemma l2_inv7_step3:
  "{l2_inv7} l2_step3 Rb A B K {> l2_inv7}"
by (auto simp add: PO_hoare_defs l2_defs intro!: l2_inv7I dest: l2_inv7D [THEN [2] rev_subsetD])

lemma l2_inv7_dy_fake_msg:
  "{l2_inv7} l2_dy_fake_msg M {> l2_inv7}"
by (auto simp add: PO_hoare_defs l2_defs extr_insert_IK_eq 
            intro!: l2_inv7I 
            elim!: l2_inv7E dy_fake_msg_extr [THEN [2] rev_subsetD])

lemma l2_inv7_dy_fake_chan:
  "{l2_inv7} l2_dy_fake_chan M {> l2_inv7}"
by (auto simp add: PO_hoare_defs l2_defs 
            intro!: l2_inv7I 
            dest:  dy_fake_chan_extr_insert [THEN [2] rev_subsetD]
            elim!: l2_inv7E dy_fake_msg_extr [THEN [2] rev_subsetD])

lemma l2_inv7_lkr_others:
  "{l2_inv7 \<inter> l2_inv5} l2_lkr_others A {> l2_inv7}"
apply (auto simp add: PO_hoare_defs l2_defs 
            intro!: l2_inv7I
            dest!: extr_insert_bad [THEN [2] rev_subsetD]
            elim!: l2_inv7E l2_inv5E)
apply (auto dest: dy_fake_msg_extr [THEN [2] rev_subsetD])
done

lemma l2_inv7_lkr_after:
  "{l2_inv7 \<inter> l2_inv5} l2_lkr_after A {> l2_inv7}"
apply (auto simp add: PO_hoare_defs l2_defs 
            intro!: l2_inv7I
            dest!: extr_insert_bad [THEN [2] rev_subsetD]
            elim!: l2_inv7E l2_inv5E)
apply (auto dest: dy_fake_msg_extr [THEN [2] rev_subsetD])
done
 
lemma l2_inv7_skr:
  "{l2_inv7 \<inter> l2_inv6} l2_skr R K {> l2_inv7}"
proof (auto simp add: PO_hoare_defs l2_defs extr_insert_IK_eq intro!: l2_inv7I,
       auto elim: l2_inv7D [THEN subsetD])
  fix s
  assume HRtest: "R \<noteq> test" "R \<notin> partners"
  assume Hi: "s \<in> l2_inv7"
  assume Hi': "s \<in> l2_inv6"
  assume HRsk: "in_progress (progress s R) xsk" "guessed_frame R xsk = Some K"
  show "K \<in> synth (analz generators)"
    proof (cases "role (guessed_runs R)")
      txt \<open>first case: @{term "R"} is the initiator, then @{term "Aenc K epk"}
        is in @{term "extr (bad s) (ik s) (chan s)"} (by invariant)
        therefore either @{term "K \<in> synth (analz generators)"} which proves the goal
        or @{term "Aenc K epk \<in> generators"}, which means that
        @{term "K = NonceF (Rb$sk)"} where @{term "R"} and @{term "Rb"} are matching
        and since @{term "R"} is not partner or test, neither is
        @{term "Rb"}, and therefore @{term "K \<in> synth (analz (generators))"}\<close>
      assume HRI: "role (guessed_runs R) = Init"
      with HRsk Hi Hi' have "Aenc K (epubKF (R$kE)) \<in> synth (analz generators)"
        by (auto dest!: l2_inv7D)
      then have "K \<in> synth (analz generators) \<or> Aenc K (epubKF (R$kE)) \<in> generators"
        by (rule synth.cases, simp_all, simp add: analz_generators)
      with HRsk show ?thesis
        proof auto
          fix Rb A B
          assume HR: "guessed_runs R = \<lparr>role = Init, owner = A, partner = B\<rparr>"
                     "guessed_frame R xsk = Some (NonceF (Rb $ sk))"
          assume HRb: "guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
                      "guessed_frame Rb xpkE = Some (epubKF (R $ kE))"
          from HR HRb have "partner_runs Rb R"
            by (auto simp add: partner_runs_def matching_def)
          with HRtest have "Rb \<noteq> test \<and> Rb \<notin> partners"
            by (auto dest: partner_test, simp add:partners_def)
          then show "NonceF (Rb $ sk) \<in> analz generators"
            by blast
        qed
    next
      txt \<open>second case: @{term "R"} is the Responder, then @{term "K"} is @{term "R$sk"}
        which is in @{term "synth (analz (generators))"}
        since @{term "R"} is not test or partner\<close>
      assume HRI: "role (guessed_runs R) = Resp"
      with HRsk HRtest show ?thesis
        by auto
    qed
qed

lemmas l2_inv7_trans_aux =
  l2_inv7_step1 l2_inv7_step2 l2_inv7_step3
  l2_inv7_dy_fake_msg l2_inv7_dy_fake_chan
  l2_inv7_lkr_others l2_inv7_lkr_after l2_inv7_skr

lemma l2_inv7_trans [iff]:
  "{l2_inv7 \<inter> l2_inv1 \<inter> l2_inv2 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> l2_inv6} trans l2 {> l2_inv7}"
by (auto simp add: l2_nostep_defs intro:l2_inv7_trans_aux)

lemma PO_l2_inv7 [iff]: "reach l2 \<subseteq> l2_inv7"
by (rule_tac J="l2_inv1 \<inter> l2_inv2 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> l2_inv6" in inv_rule_incr) (auto)

lemma l2_inv7_aux:
  "NonceF (R$sk) \<in> analz (ik s) \<Longrightarrow> s \<in> l2_inv7 \<Longrightarrow> R \<noteq> test \<and> R \<notin> partners"
proof -
  assume H:"s \<in> l2_inv7" and H':"NonceF (R$sk) \<in> analz (ik s)"
  then have H'':"NonceF (R$sk) \<in> analz (extr (bad s) (ik s) (chan s))"
    by (auto elim: analz_monotone)
  from H have "analz (extr (bad s) (ik s) (chan s)) \<subseteq> analz (synth (analz generators))"
    by (blast dest: analz_mono intro: l2_inv7D)
  with H'' have "NonceF (R$sk) \<in> analz generators"
    by auto
  then have "NonceF (R$sk) \<in> generators"
    by (simp add: analz_generators)
  then show ?thesis
    by auto
qed


subsubsection \<open>inv8\<close>
text \<open>Form of the secrets = nonces generated by test or partners\<close>
(**************************************************************************************************)
definition
  l2_inv8 :: "l2_state set"
where
  "l2_inv8 \<equiv> {s.
    secret s \<subseteq> {NonceF (R$sk) | R. R = test \<or> R \<in> partners}
  }"

lemmas l2_inv8I = l2_inv8_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv8E [elim] = l2_inv8_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv8D = l2_inv8_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv8_init [iff]:
  "init l2 \<subseteq> l2_inv8"
by (auto simp add: l2_def l2_init_def l2_inv8_def)

lemma l2_inv8_trans [iff]:
  "{l2_inv8 \<inter> l2_inv1 \<inter> l2_inv3} trans l2 {> l2_inv8}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv8I)
apply (auto simp add: l2_defs dy_fake_chan_def)
apply (auto simp add: partners_def partner_runs_def matching_def dest!: l2_inv3D)
apply (simp_all add: can_signal_def)
done

lemma PO_l2_inv8 [iff]: "reach l2 \<subseteq> l2_inv8"
by (rule_tac J="l2_inv1 \<inter> l2_inv3" in inv_rule_incr) (auto)


(**************************************************************************************************)
subsection \<open>Refinement\<close>
(**************************************************************************************************)

text \<open>mediator function\<close>
definition 
  med12s :: "l2_obs \<Rightarrow> l1_obs"
where
  "med12s t \<equiv> \<lparr>
    ik = ik t,
    secret = secret t,
    progress = progress t,
    signals = signals t
    \<rparr>"


text \<open>relation between states\<close>
definition
  R12s :: "(l1_state * l2_state) set"
where
  "R12s \<equiv> {(s,s').
    s = med12s s'
    }"

lemmas R12s_defs = R12s_def med12s_def


lemma can_signal_R12 [simp]:
  "(s1, s2) \<in> R12s \<Longrightarrow>
   can_signal s1 A B \<longleftrightarrow> can_signal s2 A B"
by (auto simp add: can_signal_def R12s_defs)

text \<open>protocol events\<close>

lemma l2_step1_refines_step1:
  "{R12s} l1_step1 Ra A B, l2_step1 Ra A B {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l1_step1_def l2_step1_def)

lemma l2_step2_refines_step2:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv7)} 
     l1_step2 Rb A B KE, l2_step2 Rb A B KE 
   {>R12s}"
apply (auto simp add: PO_rhoare_defs R12s_defs l1_step2_def, simp_all add: l2_step2_def)
apply (auto dest!: l2_inv7_aux l2_inv2D)
done

text \<open>auxiliary lemma needed to prove that the nonce received by the test in step 3
comes from a partner\<close>
lemma l2_step3_partners:
  "guessed_runs test = \<lparr>role = Init, owner = A, partner = B\<rparr> \<Longrightarrow>
   guessed_frame test xsk = Some (NonceF (Rb$sk)) \<Longrightarrow>
   guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr> \<Longrightarrow>
   guessed_frame Rb xpkE = Some (epubKF (test $ kE)) \<Longrightarrow>
   Rb \<in> partners"
by (auto simp add: partners_def partner_runs_def matching_def)

lemma l2_step3_refines_step3:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv3 \<inter> l2_inv7)} 
      l1_step3 Ra A B K, l2_step3 Ra A B K 
   {>R12s}"
apply (auto simp add: PO_rhoare_defs R12s_defs l1_step3_def, simp_all add: l2_step3_def)
apply (auto dest!: l2_inv3D l2_inv7_aux intro:l2_step3_partners)
apply (auto simp add: can_signal_def)
done


text \<open>attacker events\<close>
lemma l2_dy_fake_chan_refines_skip:
  "{R12s} Id, l2_dy_fake_chan M {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_defs)


lemma l2_dy_fake_msg_refines_learn:
  "{R12s \<inter> UNIV \<times> l2_inv7 \<inter> UNIV \<times> l2_inv8} l1_learn m, l2_dy_fake_msg m {>R12s}"
apply (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)
apply (drule Fake_insert_dy_fake_msg, erule l2_inv7D)
apply (auto simp add: analz_generators dest!: l2_inv8D)
apply (drule subsetD, simp, drule subsetD, simp, auto) (*change this ?*)
done

text \<open>compromising events\<close>
lemma l2_lkr_others_refines_skip:
  "{R12s} Id, l2_lkr_others A {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)

lemma l2_lkr_after_refines_skip:
  "{R12s} Id, l2_lkr_after A {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)

lemma l2_skr_refines_learn:
  "{R12s \<inter> UNIV \<times> l2_inv7 \<inter> UNIV \<times> l2_inv6 \<inter> UNIV \<times> l2_inv8} l1_learn K, l2_skr R K {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)
  fix s :: l2_state fix x
  assume H:"s \<in> l2_inv7" "s \<in> l2_inv6"
         "R \<notin> partners" "R \<noteq> test" "run_ended (progress s R)" "guessed_frame R xsk = Some K"
  assume Hx:"x \<in> synth (analz (insert K (ik s)))"
  assume "x \<in> secret s" "s \<in> l2_inv8"
  then obtain R where "x = NonceF (R$sk)" and "R = test \<or> R \<in> partners"
    by auto
  moreover from H have "s \<lparr>ik := insert K (ik s)\<rparr> \<in> l2_inv7"
    by (auto intro: hoare_apply [OF l2_inv7_skr] simp add: l2_defs)
  ultimately show False using Hx 
    by (auto dest: l2_inv7_aux [rotated 1])
qed

 
text \<open>refinement proof\<close>
lemmas l2_trans_refines_l1_trans = 
  l2_dy_fake_msg_refines_learn l2_dy_fake_chan_refines_skip
  l2_lkr_others_refines_skip l2_lkr_after_refines_skip l2_skr_refines_learn
  l2_step1_refines_step1 l2_step2_refines_step2 l2_step3_refines_step3 

lemma l2_refines_init_l1 [iff]:
  "init l2 \<subseteq> R12s `` (init l1)"
by (auto simp add: R12s_defs l1_defs l2_loc_defs)

lemma l2_refines_trans_l1 [iff]:
  "{R12s \<inter> (UNIV \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv6 \<inter> l2_inv7 \<inter> l2_inv8))} trans l1, trans l2 {> R12s}"
by (auto 0 3 simp add: l1_def l2_def l1_trans_def l2_trans_def
             intro!: l2_trans_refines_l1_trans)

lemma PO_obs_consistent_R12s [iff]: 
  "obs_consistent R12s med12s l1 l2"
by (auto simp add: obs_consistent_def R12s_def med12s_def l2_defs)

lemma l2_refines_l1 [iff]:
  "refines 
     (R12s \<inter> 
      (reach l1 \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> l2_inv6 \<inter> l2_inv7 \<inter> l2_inv8)))
     med12s l1 l2"
by (rule Refinement_using_invariants, auto)

lemma l2_implements_l1 [iff]:
  "implements med12s l1 l2"
by (rule refinement_soundness) (auto)


subsection \<open>Derived invariants\<close>
(**************************************************************************************************)
text \<open>
  We want to prove @{term "l2_secrecy"}:
  @{term "dy_fake_msg (bad s) (ik s) (chan s) \<inter> secret s = {}"}
  but by refinement we only get @{term "l2_partial_secrecy"}:
  @{term "synth (analz (ik s)) \<inter> secret s = {}"}
  This is fine, since a message in
  @{term "dy_fake_msg (bad s) (ik s) (chan s)"} could be added to @{term "ik s"},
  and @{term "l2_partial_secrecy"} would still hold for this new state.
\<close>

definition
  l2_partial_secrecy :: "('a l2_state_scheme) set"
where
  "l2_partial_secrecy \<equiv> {s. synth (analz (ik s)) \<inter> secret s = {}}"


lemma l2_obs_partial_secrecy [iff]: "oreach l2 \<subseteq> l2_partial_secrecy"
apply (rule external_invariant_translation 
         [OF l1_obs_secrecy _ l2_implements_l1])
apply (auto simp add: med12s_def s0_secrecy_def l2_partial_secrecy_def)
done

lemma l2_oreach_dy_fake_msg:
  "s \<in> oreach l2 \<Longrightarrow> x \<in> dy_fake_msg (bad s) (ik s) (chan s) \<Longrightarrow> s \<lparr>ik := insert x (ik s)\<rparr> \<in> oreach l2"
apply (auto simp add: oreach_def, rule, simp_all, simp add: l2_def l2_trans_def l2_dy_fake_msg_def)
apply blast
done


definition 
  l2_secrecy :: "('a l2_state_scheme) set"
where
  "l2_secrecy \<equiv> {s. dy_fake_msg (bad s) (ik s) (chan s) \<inter> secret s = {}}"

lemma l2_obs_secrecy [iff]: "oreach l2 \<subseteq> l2_secrecy"
apply (auto simp add:l2_secrecy_def)
apply (drule l2_oreach_dy_fake_msg, simp_all)
apply (drule l2_obs_partial_secrecy [THEN [2] rev_subsetD], simp add: l2_partial_secrecy_def)
apply blast
done


lemma l2_secrecy [iff]: "reach l2 \<subseteq> l2_secrecy"
by (rule external_to_internal_invariant [OF l2_obs_secrecy], auto)


abbreviation "l2_iagreement \<equiv> l1_iagreement"

lemma l2_obs_iagreement [iff]: "oreach l2 \<subseteq> l2_iagreement"
apply (rule external_invariant_translation 
         [OF l1_obs_iagreement _ l2_implements_l1])
apply (auto simp add: med12s_def l1_iagreement_def)
done

lemma l2_iagreement [iff]: "reach l2 \<subseteq> l2_iagreement"
by (rule external_to_internal_invariant [OF l2_obs_iagreement], auto)

end
