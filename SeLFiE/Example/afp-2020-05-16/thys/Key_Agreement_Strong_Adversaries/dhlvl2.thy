(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  dhlvl2.thy (Isabelle/HOL 2016-1)
  ID:      $Id: dhlvl2.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-2 Diffie-Hellman channel protocol using authenticated channels.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Authenticated Diffie-Hellman Protocol (L2)\<close>

theory dhlvl2
imports dhlvl1 Channels
begin

declare domIff [simp, iff del]

(**************************************************************************************************)
subsection \<open>State and Events\<close>
(**************************************************************************************************)

text \<open>Initial compromise.\<close>
consts
  bad_init :: "agent set" 

specification (bad_init)
  bad_init_spec: "test_owner \<notin> bad_init \<and> test_partner \<notin> bad_init"
by auto


text \<open>Level 2 state.\<close>

record l2_state = 
  l1_state +
  chan :: "chan set"
  bad :: "agent set"


type_synonym l2_obs = "l2_state"

type_synonym
  l2_pred = "l2_state set"

type_synonym
  l2_trans = "(l2_state \<times> l2_state) set"


text \<open>Attacker events.\<close>

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


text \<open>Partnering.\<close>

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

text \<open>The unicity of the parther is actually protocol dependent:
it only holds if there are generated fresh nonces (which identify the runs) in the frames.\<close>

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
      with Init Hm' have "guessed_frame R xgnx = Some (Exp Gen (NonceF (R'$nx)))"
        by (simp add: matching_def)
      moreover from Hrole Hm'' have "guessed_frame R xgnx = Some (Exp Gen (NonceF (R''$nx)))"
        by (simp add: matching_def)
      ultimately show ?thesis by (auto dest: Exp_Gen_inj)
    next
      case Resp
      with H' partner_symmetric [OF H''] have Hrole:"role (guessed_runs R) = Init"
                                                    "role (guessed_runs R'') = Resp"
        by (auto simp add: partner_runs_def)
      with Resp Hm' have "guessed_frame R xgny = Some (Exp Gen (NonceF (R'$ny)))"
        by (simp add: matching_def)
      moreover from Hrole Hm'' have "guessed_frame R xgny = Some (Exp Gen (NonceF (R''$ny)))"
        by (simp add: matching_def)
      ultimately show ?thesis by (auto dest: Exp_Gen_inj)
    qed
qed

lemma partner_test:
  "R \<in> partners \<Longrightarrow> partner_runs R R' \<Longrightarrow> R' = test"
by (auto intro!:partner_unique simp add:partners_def partner_symmetric)


text \<open>Compromising events.\<close>

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


text \<open>Protocol events:
\begin{itemize}
  \item step 1: create @{term "Ra"}, @{term "A"} generates @{term "nx"},
    computes and insecurely sends $@{term "g"}^@{term "nx"}$
  \item step 2: create @{term "Rb"}, @{term "B"} receives $@{term "g"}^@{term "nx"}$ insecurely,
    generates @{term "ny"}, computes $@{term "g"}^@{term "ny"}$,
    authentically sends $(@{term "g"}^@{term "ny"}, @{term "g"}^@{term "nx"})$,
    computes $@{term "g"}^@{term "nx*ny"}$,
    emits a running signal for @{term "Init"}, $@{term "g"}^@{term "nx*ny"}$
  \item step 3: @{term "A"} receives $@{term "g"}^@{term "ny"}$ and $@{term "g"}^@{term "nx"}$
    authentically,
    sends $(@{term "g"}^@{term "nx"}, @{term "g"}^@{term "ny"})$ authentically,
    computes $@{term "g"}^@{term "ny*nx"}$, emits a commit signal for @{term "Init"},
    $@{term "g"}^@{term "ny*nx"}$, a running signal for @{term "Resp"}, $@{term "g"}^@{term "ny*nx"}$,
    declares the secret $@{term "g"}^@{term "ny*nx"}$
  \item step 4: @{term "B"} receives $@{term "g"}^@{term "nx"}$ and $@{term "g"}^@{term "ny"}$
    authentically,
    emits a commit signal for @{term "Resp"}, $@{term "g"}^@{term "nx*ny"}$,
    declares the secret $@{term "g"}^@{term "nx*ny"}$
\end{itemize}
\<close>

definition
    l2_step1 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> l2_trans"
where
  "l2_step1 Ra A B \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (progress s) \<and>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      progress := (progress s)(Ra \<mapsto> {xnx, xgnx}),
      chan := {Insec A B (Exp Gen (NonceF (Ra$nx)))} \<union> (chan s)
    \<rparr>
  }"


definition
  l2_step2 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step2 Rb A B gnx \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    Rb \<notin> dom (progress s) \<and>
    guessed_frame Rb xgnx = Some gnx \<and>
    guessed_frame Rb xsk = Some (Exp gnx (NonceF (Rb$ny))) \<and>
    Insec A B gnx \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Rb \<mapsto> {xny, xgny, xgnx, xsk}),
            chan := {Auth B A \<langle>Number 0, Exp Gen (NonceF (Rb$ny)), gnx\<rangle>} \<union> (chan s),
            signalsInit := if can_signal s A B then
                          addSignal (signalsInit s) (Running A B (Exp gnx (NonceF (Rb$ny))))
                       else
                          signalsInit s
         \<rparr>
  }"  


definition
  l2_step3 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step3 Ra A B gny \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    progress s Ra = Some {xnx, xgnx} \<and>
    guessed_frame Ra xgny = Some gny \<and>
    guessed_frame Ra xsk = Some (Exp gny (NonceF (Ra$nx))) \<and>
    Auth B A \<langle>Number 0, gny, Exp Gen (NonceF (Ra$nx))\<rangle> \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Ra \<mapsto> {xnx, xgnx, xgny, xsk, xEnd}),
            chan := {Auth A B \<langle>Number 1, Exp Gen (NonceF (Ra$nx)), gny\<rangle>} \<union> chan s,
            secret := {x. x = Exp gny (NonceF (Ra$nx)) \<and> Ra = test} \<union> secret s,
            signalsInit := if can_signal s A B then
                         addSignal (signalsInit s) (Commit A B (Exp gny (NonceF (Ra$nx))))
                       else
                         signalsInit s,
            signalsResp := if can_signal s A B then
                         addSignal (signalsResp s) (Running A B (Exp gny (NonceF (Ra$nx))))
                       else
                         signalsResp s
          \<rparr>
  }"


definition
  l2_step4 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step4 Rb A B gnx \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    progress s Rb = Some {xny, xgnx, xgny, xsk} \<and>
    guessed_frame Rb xgnx = Some gnx \<and>
    Auth A B \<langle>Number 1, gnx, Exp Gen (NonceF (Rb$ny))\<rangle> \<in> chan s \<and>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Rb \<mapsto> {xny, xgnx, xgny, xsk, xEnd}),
            secret := {x. x = Exp gnx (NonceF (Rb$ny)) \<and> Rb = test} \<union> secret s,
            signalsResp := if can_signal s A B then
                             addSignal (signalsResp s) (Commit A B (Exp gnx (NonceF (Rb$ny))))
                           else
                             signalsResp s
          \<rparr>
  }"

text \<open>Specification.\<close>
definition 
  l2_init :: "l2_state set"
where
  "l2_init \<equiv> { \<lparr>
    ik = {},
    secret = {},
    progress = Map.empty,
    signalsInit = \<lambda>x. 0,
    signalsResp = \<lambda>x. 0,
    chan = {},
    bad = bad_init
    \<rparr>}"

definition 
  l2_trans :: "l2_trans" where
  "l2_trans \<equiv> (\<Union>m M X Rb Ra A B K.
     l2_step1 Ra A B \<union>
     l2_step2 Rb A B X \<union>
     l2_step3 Ra A B X \<union>
     l2_step4 Rb A B X \<union>
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
  l2_step1_def l2_step2_def l2_step3_def l2_step4_def
  l2_def l2_init_def l2_trans_def
  l2_dy_fake_chan_def l2_dy_fake_msg_def
  l2_lkr_after_def l2_lkr_others_def l2_skr_def

lemmas l2_defs = l2_loc_defs ik_dy_def

lemmas l2_nostep_defs = l2_def l2_init_def l2_trans_def


lemma l2_obs_id [simp]: "obs l2 = id"
by (simp add: l2_def)


text \<open>Once a run is finished, it stays finished, therefore if the test is not finished at some
point then it was not finished before either.\<close>

declare domIff [iff]
lemma l2_run_ended_trans:
  "run_ended (progress s R) \<Longrightarrow>
   (s, s') \<in> trans l2 \<Longrightarrow>
   run_ended (progress s' R)"
apply (auto simp add: l2_nostep_defs)
apply (auto simp add: l2_defs)
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

text \<open>If @{term "can_signal s A B"}
(i.e., @{term "A"}, @{term "B"} are the test session agents and the test is not finished),
then A and B are honest.\<close>

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

text \<open>If @{term "Auth B A \<langle>Number 0, gny, Exp Gen (NonceF (Ra$nx))\<rangle> \<in> chan s"} and @{term "A"},
  @{term "B"} are honest then the message has indeed been sent by a responder run (etc).\<close>

definition
  l2_inv2 :: "l2_state set"
where
  "l2_inv2 \<equiv> {s. \<forall> Ra A B gny.
    Auth B A \<langle>Number 0, gny, Exp Gen (NonceF (Ra$nx))\<rangle> \<in> chan s  \<longrightarrow>
    A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
    (\<exists> Rb. guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
           in_progressS (progress s Rb) {xny, xgnx, xgny, xsk} \<and>
           gny = Exp Gen (NonceF (Rb$ny)) \<and>
           guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))))
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

text \<open>If \<open>Auth A B \<langle>Number 1, gnx, Exp Gen (NonceF (Rb$ny))\<rangle> \<in> chan s\<close> and @{term "A"},
  @{term "B"} are honest
  then the message has indeed been sent by an initiator run (etc).\<close>

definition
  l2_inv3 :: "l2_state set"
where
  "l2_inv3 \<equiv> {s. \<forall> Rb A B gnx.
     Auth A B \<langle>Number 1, gnx, Exp Gen (NonceF (Rb$ny))\<rangle> \<in> chan s \<longrightarrow>
     A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
       (\<exists> Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
              in_progressS (progress s Ra) {xnx, xgnx, xgny, xsk, xEnd} \<and>
              guessed_frame Ra xgnx = Some gnx \<and>
              guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))))
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
apply (simp_all add: domIff insert_ident)
apply force+
done

lemma PO_l2_inv3 [iff]: "reach l2 \<subseteq> l2_inv3"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv4\<close>
(**************************************************************************************************)

text \<open>For an initiator, the session key is always \<open>gny^nx\<close>.\<close>

definition
  l2_inv4 :: "l2_state set"
where
  "l2_inv4 \<equiv> {s. \<forall>Ra A B gny.
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<longrightarrow>
    in_progress (progress s Ra) xsk \<longrightarrow>
    guessed_frame Ra xgny = Some gny \<longrightarrow>
    guessed_frame Ra xsk = Some (Exp gny (NonceF (Ra$nx)))
  }"

lemmas l2_inv4I = l2_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv4E [elim] = l2_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv4D = l2_inv4_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv4_init [iff]:
  "init l2 \<subseteq> l2_inv4"
by (auto simp add: l2_def l2_init_def l2_inv4_def)

lemma l2_inv4_trans [iff]:
  "{l2_inv4} trans l2 {> l2_inv4}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv4I)
apply (auto simp add: l2_defs dy_fake_chan_def)
done

lemma PO_l2_inv4 [iff]: "reach l2 \<subseteq> l2_inv4"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv4'\<close>
(**************************************************************************************************)

text \<open>For a responder, the session key is always \<open>gnx^ny\<close>.\<close>

definition
  l2_inv4' :: "l2_state set"
where
  "l2_inv4' \<equiv> {s. \<forall>Rb A B gnx.
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<longrightarrow>
    in_progress (progress s Rb) xsk \<longrightarrow>
    guessed_frame Rb xgnx = Some gnx \<longrightarrow>
    guessed_frame Rb xsk = Some (Exp gnx (NonceF (Rb$ny)))
  }"

lemmas l2_inv4'I = l2_inv4'_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv4'E [elim] = l2_inv4'_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv4'D = l2_inv4'_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv4'_init [iff]:
  "init l2 \<subseteq> l2_inv4'"
by (auto simp add: l2_def l2_init_def l2_inv4'_def)

lemma l2_inv4'_trans [iff]:
  "{l2_inv4'} trans l2 {> l2_inv4'}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv4'I)
apply (auto simp add: l2_defs dy_fake_chan_def)
done

lemma PO_l2_inv4' [iff]: "reach l2 \<subseteq> l2_inv4'"
by (rule inv_rule_basic) (auto)



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

text \<open>For a run @{term "R"} (with any role), the session key always has the form
$something^n$ where $n$ is a nonce generated by @{term "R"}.\<close>

definition
  l2_inv6 :: "l2_state set"
where
  "l2_inv6 \<equiv> {s. \<forall>R.
    in_progress (progress s R) xsk \<longrightarrow>
    (\<exists> X N.
      guessed_frame R xsk = Some (Exp X (NonceF (R$N))))
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
  "generators \<equiv> {x. \<exists> N. x = Exp Gen (Nonce N)} \<union> 
                {Exp y (NonceF (R$N)) |y N R. R \<noteq> test \<and> R \<notin> partners}"

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
apply (auto intro: synth_analz_increasing)
done

lemma l2_inv7_step2:
  "{l2_inv7} l2_step2 Rb A B gnx {> l2_inv7}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv7I, auto simp add: l2_defs)
apply (auto intro: synth_analz_increasing)
done

lemma l2_inv7_step3:
  "{l2_inv7} l2_step3 Ra A B gny {> l2_inv7}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv7I, auto simp add: l2_defs)
apply (auto intro: synth_analz_increasing)
apply (auto dest:l2_inv7D [THEN [2] rev_subsetD] dest!:extr_Chan)
done

lemma l2_inv7_step4:
  "{l2_inv7} l2_step4 Rb A B gnx {> l2_inv7}"
by (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv7I, auto simp add: l2_defs)

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

apply (auto simp add: PO_hoare_defs l2_defs  intro!: l2_inv7I)
apply (auto simp add: extr_insert_IK_eq dest!: l2_inv6D)
apply (auto intro: synth_analz_increasing)
done

lemmas l2_inv7_trans_aux =
  l2_inv7_step1 l2_inv7_step2 l2_inv7_step3 l2_inv7_step4
  l2_inv7_dy_fake_msg l2_inv7_dy_fake_chan
  l2_inv7_lkr_others l2_inv7_lkr_after l2_inv7_skr

lemma l2_inv7_trans [iff]:
  "{l2_inv7 \<inter> l2_inv5 \<inter> l2_inv6} trans l2 {> l2_inv7}"
by (auto simp add: l2_nostep_defs intro:l2_inv7_trans_aux)

lemma PO_l2_inv7 [iff]: "reach l2 \<subseteq> l2_inv7"
by (rule_tac J="l2_inv5 \<inter> l2_inv6" in inv_rule_incr) (auto)

text \<open>Auxiliary dest rule for inv7.\<close>
lemmas l2_inv7D_aux = 
  l2_inv7D [THEN [2] subset_trans, THEN synth_analz_mono, simplified, 
            THEN [2] rev_subsetD, rotated 1, OF IK_subset_extr]


subsubsection \<open>inv8: form of the secrets\<close>
(**************************************************************************************************)

definition
  l2_inv8 :: "l2_state set"
where
  "l2_inv8 \<equiv> {s.
    secret s \<subseteq> {Exp (Exp Gen (NonceF (R$N))) (NonceF (R'$N')) | N N' R R'.
                  R = test \<and> R' \<in> partners}
  }"

lemmas l2_inv8I = l2_inv8_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv8E [elim] = l2_inv8_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv8D = l2_inv8_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv8_init [iff]:
  "init l2 \<subseteq> l2_inv8"
by (auto simp add: l2_def l2_init_def l2_inv8_def)

text \<open>Steps 3 and 4 are the hard part.\<close>

lemma l2_inv8_step3:
  "{l2_inv8 \<inter> l2_inv1 \<inter> l2_inv2 \<inter> l2_inv4'} l2_step3 Ra A B gny {> l2_inv8}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv8I)
  fix s s' :: l2_state fix x
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv8" "s \<in> l2_inv2" "s \<in> l2_inv4'"
  assume Ht:"(s, s') \<in> l2_step3 Ra A B gny"
  assume Hs:"x \<in> secret s'"
  from Hs Ht have "x \<in> secret s \<or> (Ra = test \<and> x = Exp gny (NonceF (Ra$nx)))"
    by (auto simp add: l2_defs)
  with Hi Ht 
  show "\<exists>N N' R'. x = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and> R' \<in> partners"
    proof (auto dest: l2_inv8D simp add: l2_defs)
      assume Hx: "x = Exp gny (NonceF (test $ nx))"
      assume "can_signal s A B"
      with Hi have HA: "A \<notin> bad s \<and> B \<notin> bad s"
        by auto
      assume Htest: "guessed_runs test = \<lparr>role = Init, owner = A, partner = B\<rparr>"
                    "guessed_frame test xgny = Some gny"
                    "guessed_frame test xsk = Some (Exp gny (NonceF (test $ nx)))"
      assume "Auth B A \<langle>Number 0, gny, Exp Gen (NonceF (test $ nx))\<rangle> \<in> chan s"
      with Hi HA obtain Rb where HRb:
        "guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr>"
        "in_progressS (progress s Rb) {xny, xgnx, xgny, xsk}"
        "gny = Exp Gen (NonceF (Rb$ny))"
        "guessed_frame Rb xgnx = Some (Exp Gen (NonceF (test$nx)))"
        by (auto dest!: l2_inv2D)
      with Hi 
      have "guessed_frame Rb xsk = Some (Exp (Exp Gen (NonceF (Rb$ny))) (NonceF (test$nx)))"
        by (auto dest: l2_inv4'D)
      with HRb Htest have "Rb \<in> partners"
        by (auto simp add: partners_def partner_runs_def matching_def)
      with HRb have "Exp gny (NonceF (test $ nx)) = 
                        Exp (Exp Gen (NonceF (Rb $ ny))) (NonceF (test $ nx)) \<and> Rb \<in> partners"
        by auto
      then show "\<exists>N N' R'.
          Exp gny (NonceF (test $ nx)) = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and>
          R' \<in> partners"
        by blast
    qed (auto simp add: can_signal_def)
qed

lemma l2_inv8_step4:
  "{l2_inv8 \<inter> l2_inv1 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4'} l2_step4 Rb A B gnx {> l2_inv8}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv8I)
  fix s s' :: l2_state fix x
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv8" "s \<in> l2_inv3" "s \<in> l2_inv4" "s \<in> l2_inv4'"
  assume Ht:"(s, s') \<in> l2_step4 Rb A B gnx"
  assume Hs:"x \<in> secret s'"
  from Hs Ht have "x \<in> secret s \<or> (Rb = test \<and> x = Exp gnx (NonceF (Rb$ny)))"
    by (auto simp add: l2_defs)
  with Hi Ht 
  show "\<exists>N N' R'. x = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and> R' \<in> partners"
    proof (auto dest: l2_inv8D simp add: l2_defs)
      assume Hx: "x = Exp gnx (NonceF (test $ ny))"
      assume "can_signal s A B"
      with Hi have HA: "A \<notin> bad s \<and> B \<notin> bad s"
        by auto
      assume Htest: "guessed_runs test = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
                    "guessed_frame test xgnx = Some gnx"
      assume "progress s test = Some {xny, xgnx, xgny, xsk}"
      with Htest Hi have Htest': "guessed_frame test xsk = Some (Exp gnx (NonceF (test $ ny)))"
        by (auto dest: l2_inv4'D)
      assume "Auth A B \<langle>Number (Suc 0), gnx, Exp Gen (NonceF (test $ ny))\<rangle> \<in> chan s"
      with Hi HA obtain Ra where HRa:
        "guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
        "in_progressS (progress s Ra) {xnx, xgnx, xgny, xsk, xEnd}"
        "gnx = Exp Gen (NonceF (Ra$nx))"
        "guessed_frame Ra xgny = Some (Exp Gen (NonceF (test$ny)))"
        by (auto dest!: l2_inv3D)
      with Hi 
      have "guessed_frame Ra xsk = Some (Exp (Exp Gen (NonceF (Ra$nx))) (NonceF (test$ny)))"
        by (auto dest: l2_inv4D)
      with HRa Htest Htest' have "Ra \<in> partners"
        by (auto simp add: partners_def partner_runs_def matching_def)
      with HRa have "Exp gnx (NonceF (test $ ny)) = 
                        Exp (Exp Gen (NonceF (Ra $ nx))) (NonceF (test $ ny)) \<and> Ra \<in> partners"
        by auto
      then show "\<exists>N N' R'.
          Exp gnx (NonceF (test $ ny)) = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and>
          R' \<in> partners"
        by auto
    qed (auto simp add: can_signal_def)
qed


lemma l2_inv8_trans [iff]:
  "{l2_inv8 \<inter> l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4'} trans l2 {> l2_inv8}"
apply (auto simp add: l2_nostep_defs intro!: l2_inv8_step3 l2_inv8_step4)
apply (auto simp add: PO_hoare_defs intro!: l2_inv8I)
apply (auto simp add: l2_defs dy_fake_chan_def dest: l2_inv8D)
done

lemma PO_l2_inv8 [iff]: "reach l2 \<subseteq> l2_inv8"
by (rule_tac J="l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4'" in inv_rule_incr) (auto)


text \<open>Auxiliary destruction rule for inv8.\<close>

lemma Exp_Exp_Gen_synth: 
  "Exp (Exp Gen X) Y \<in> synth H \<Longrightarrow> Exp (Exp Gen X) Y \<in> H \<or> X \<in> synth H \<or> Y \<in> synth H"
by (erule synth.cases, auto dest: Exp_Exp_Gen_inj2)

lemma l2_inv8_aux:
  "s \<in> l2_inv8 \<Longrightarrow>
   x \<in> secret s \<Longrightarrow>
   x \<notin> synth (analz generators)"
apply (auto simp add: analz_generators dest!: l2_inv8D [THEN [2] rev_subsetD])
apply (auto dest!: Exp_Exp_Gen_synth Exp_Exp_Gen_inj2)
done

(**************************************************************************************************)
subsection \<open>Refinement\<close>
(**************************************************************************************************)

text \<open>Mediator function.\<close>
definition
  med12s :: "l2_obs \<Rightarrow> l1_obs"
where
  "med12s t \<equiv> \<lparr>
    ik = ik t,
    secret = secret t,
    progress = progress t,
    signalsInit = signalsInit t,
    signalsResp = signalsResp t
    \<rparr>"


text \<open>Relation between states.\<close>

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

text \<open>Protocol events.\<close>

lemma l2_step1_refines_step1:
  "{R12s} l1_step1 Ra A B, l2_step1 Ra A B {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l1_step1_def l2_step1_def)

lemma l2_step2_refines_step2:
  "{R12s} l1_step2 Rb A B gnx, l2_step2 Rb A B gnx {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l1_step2_def, simp_all add: l2_step2_def)

text \<open>For step3 and 4, we prove the level 1 guard, i.e.,
"the future session key is not in @{term "synth (analz (ik s))"}"
  using the fact that inv8 also holds for the future state in which the session key is already in 
  @{term "secret s"}.\<close>

lemma l2_step3_refines_step3:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv4' \<inter> l2_inv7 \<inter> l2_inv8)} 
      l1_step3 Ra A B gny, l2_step3 Ra A B gny 
   {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs)
  fix s s'
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv2" "s \<in> l2_inv4'" "s \<in> l2_inv7" 
  assume Ht: "(s, s') \<in> l2_step3 Ra A B gny"
  assume "s \<in> l2_inv8"
  with Hi Ht l2_inv8_step3 have Hi':"s' \<in> l2_inv8"
    by (auto simp add: PO_hoare_defs, blast)
  from Ht have "Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<in> secret s'"
    by (auto simp add: l2_defs)
  with Hi' have "Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<notin> synth (analz generators)"
    by (auto dest: l2_inv8_aux)
  with Hi have G2:"Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<notin> synth (analz (ik s))"
    by (auto dest!: l2_inv7D_aux)
  from Ht Hi have G1:
    "can_signal s A B \<longrightarrow> (\<exists> Rb. guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
           in_progressS (progress s Rb) {xny, xgnx, xgny, xsk} \<and>
           gny = Exp Gen (NonceF (Rb$ny)) \<and>
           guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))))"
   by (auto dest!: l2_inv2D [rotated 2] simp add: l2_defs)

  with Ht G1 G2 show
    "(\<lparr> ik = ik s, secret = secret s, progress = progress s, 
        signalsInit = signalsInit s, signalsResp = signalsResp s \<rparr>,
      \<lparr> ik = ik s', secret = secret s', progress = progress s', 
        signalsInit = signalsInit s', signalsResp = signalsResp s' \<rparr>)
           \<in> l1_step3 Ra A B gny"
    apply (auto simp add: l2_step3_def, auto simp add: l1_step3_def)
    apply (auto simp add: can_signal_def)
    done
qed

lemma l2_step4_refines_step4:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4' \<inter> l2_inv7 \<inter> l2_inv8)} 
      l1_step4 Rb A B gnx, l2_step4 Rb A B gnx
   {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs)
  fix s s'
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv3" "s \<in> l2_inv4" "s \<in> l2_inv4'" "s \<in> l2_inv7" 
  assume Ht: "(s, s') \<in> l2_step4 Rb A B gnx"
  assume "s \<in> l2_inv8"
  with Hi Ht l2_inv8_step4 have Hi':"s' \<in> l2_inv8"
    by (auto simp add: PO_hoare_defs, blast)
  from Ht have "Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<in> secret s'"
    by (auto simp add: l2_defs)
  with Hi' have "Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<notin> synth (analz generators)"
    by (auto dest: l2_inv8_aux)
  with Hi have G2:"Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<notin> synth (analz (ik s))"
    by (auto dest!: l2_inv7D_aux)
  from Ht Hi have G1:
    "can_signal s A B \<longrightarrow> (\<exists> Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
              in_progressS (progress s Ra) {xnx, xgnx, xgny, xsk, xEnd} \<and>
              guessed_frame Ra xgnx = Some gnx \<and>
              guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))))"
   by (auto dest!: l2_inv3D [rotated 2] simp add: l2_defs)

  with Ht G1 G2 show
    "(\<lparr> ik = ik s, secret = secret s, progress = progress s, 
        signalsInit = signalsInit s, signalsResp = signalsResp s \<rparr>,
      \<lparr> ik = ik s', secret = secret s', progress = progress s', 
        signalsInit = signalsInit s', signalsResp = signalsResp s' \<rparr>)
           \<in> l1_step4 Rb A B gnx"
    apply (auto simp add: l2_step4_def, auto simp add: l1_step4_def)
    apply (auto simp add: can_signal_def)
    done
qed

text \<open>Attacker events.\<close>

lemma l2_dy_fake_chan_refines_skip:
  "{R12s} Id, l2_dy_fake_chan M {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_defs)


lemma l2_dy_fake_msg_refines_learn:
  "{R12s \<inter> UNIV \<times> (l2_inv7 \<inter> l2_inv8)} l1_learn m, l2_dy_fake_msg m {>R12s}"
apply (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)
apply (drule Fake_insert_dy_fake_msg, erule l2_inv7D)
apply (auto dest!: l2_inv8_aux)
done

text \<open>Compromising events.\<close>

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
         "R \<notin> partners" "R \<noteq> test" "in_progress (progress s R) xsk" "guessed_frame R xsk = Some K"
  assume Hx:"x \<in> synth (analz (insert K (ik s)))"
  assume "x \<in> secret s" "s \<in> l2_inv8"
  then obtain R R' N N' where Hx':"x = Exp (Exp Gen (NonceF (R$N))) (NonceF (R'$N'))"
                                "R = test \<and> R' \<in> partners"
    by (auto dest!: l2_inv8D subsetD)
  from H have "s \<lparr>ik := insert K (ik s)\<rparr> \<in> l2_inv7"
    by (auto intro: hoare_apply [OF l2_inv7_skr] simp add: l2_defs)
  with Hx have "x \<in> synth (analz (generators))"
    by (auto dest: l2_inv7D_aux)
  with Hx' show False
    by (auto dest!: Exp_Exp_Gen_synth dest: Exp_Exp_Gen_inj2 simp add: analz_generators)
qed

text \<open>Refinement proof.\<close>

lemmas l2_trans_refines_l1_trans = 
  l2_dy_fake_msg_refines_learn l2_dy_fake_chan_refines_skip
  l2_lkr_others_refines_skip l2_lkr_after_refines_skip l2_skr_refines_learn
  l2_step1_refines_step1 l2_step2_refines_step2 l2_step3_refines_step3 l2_step4_refines_step4

lemma l2_refines_init_l1 [iff]:
  "init l2 \<subseteq> R12s `` (init l1)"
by (auto simp add: R12s_defs l1_defs l2_loc_defs)

lemma l2_refines_trans_l1 [iff]:
  "{R12s \<inter> (UNIV \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4' \<inter> 
                     l2_inv6 \<inter> l2_inv7 \<inter> l2_inv8))}
     trans l1, trans l2
   {> R12s}"
by (auto 0 3 simp add: l1_def l2_def l1_trans_def l2_trans_def
             intro: l2_trans_refines_l1_trans) 


lemma PO_obs_consistent_R12s [iff]: 
  "obs_consistent R12s med12s l1 l2"
by (auto simp add: obs_consistent_def R12s_def med12s_def l2_defs)

lemma l2_refines_l1 [iff]:
  "refines 
     (R12s \<inter> 
      (reach l1 \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv4' \<inter> l2_inv5 \<inter>
                                                  l2_inv6 \<inter> l2_inv7 \<inter> l2_inv8)))
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
  "\<lbrakk> s \<in> oreach l2; x \<in> dy_fake_msg (bad s) (ik s) (chan s) \<rbrakk>
 \<Longrightarrow> s \<lparr>ik := insert x (ik s)\<rparr> \<in> oreach l2"
apply (auto simp add: oreach_def, rule, simp_all, 
       simp add: l2_def l2_trans_def l2_dy_fake_msg_def)
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


abbreviation "l2_iagreement_Init \<equiv> l1_iagreement_Init"

lemma l2_obs_iagreement_Init [iff]: "oreach l2 \<subseteq> l2_iagreement_Init"
apply (rule external_invariant_translation 
         [OF l1_obs_iagreement_Init _ l2_implements_l1])
apply (auto simp add: med12s_def l1_iagreement_Init_def)
done

lemma l2_iagreement_Init [iff]: "reach l2 \<subseteq> l2_iagreement_Init"
by (rule external_to_internal_invariant [OF l2_obs_iagreement_Init], auto)

abbreviation "l2_iagreement_Resp \<equiv> l1_iagreement_Resp"

lemma l2_obs_iagreement_Resp [iff]: "oreach l2 \<subseteq> l2_iagreement_Resp"
apply (rule external_invariant_translation 
         [OF l1_obs_iagreement_Resp _ l2_implements_l1])
apply (auto simp add: med12s_def l1_iagreement_Resp_def)
done

lemma l2_iagreement_Resp [iff]: "reach l2 \<subseteq> l2_iagreement_Resp"
by (rule external_to_internal_invariant [OF l2_obs_iagreement_Resp], auto)

end
