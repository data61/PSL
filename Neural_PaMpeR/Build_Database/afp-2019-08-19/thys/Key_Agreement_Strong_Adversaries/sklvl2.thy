(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  sklvl2.thy (Isabelle/HOL 2016-1)
  ID:      $Id: sklvl2.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Level-2 SKEME/IKEv1 channel protocol using confidential channels and 
  dynamically keyed HMACs. Refines model sklvl1.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>SKEME Protocol (L2)\<close>

theory sklvl2
imports sklvl1 Channels
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
  skl1_state +
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
it only holds if there are generated fresh nonces (which identify the runs) in the frames\<close>
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


text \<open>Protocol events (with $K=H(ni, nr)$):
\begin{itemize}
\item step 1: create @{term "Ra"}, @{term "A"} generates @{term "nx"} and @{term "ni"},
  confidentially sends @{term "ni"},
  computes and insecurely sends $@{term "g"}^@{term "nx"}$
\item step 2: create @{term "Rb"}, @{term "B"} receives @{term "ni"} (confidentially)
  and $@{term "g"}^@{term "nx"}$ (insecurely),
  generates @{term "ny"} and @{term "nr"},
  confidentially sends @{term "nr"}, insecurely sends $@{term "g"}^@{term "ny"}$ and
  $MAC_K(@{term "g"}^@{term "nx"}, @{term "g"}^@{term "ny"}, @{term "B"}, @{term "A"})$
  computes $@{term "g"}^@{term "nx*ny"}$,
  emits a running signal for @{term "Init"}, @{term "ni"}, @{term "nr"}, $@{term "g"}^@{term "nx*ny"}$
\item step 3: @{term "A"} receives @{term "nr"} confidentially,
  and $@{term "g"}^@{term "ny"}$ and the MAC insecurely,
  sends $MAC_K(@{term "g"}^@{term "ny"}, @{term "g"}^@{term "nx"}, @{term "A"}, @{term "B"})$
  insecurely, computes $@{term "g"}^@{term "ny*nx"}$, emits a commit signal for @{term "Init"},
  @{term "ni"}, @{term "nr"}, $@{term "g"}^@{term "ny*nx"}$,
  a running signal for @{term "Resp"}, @{term "ni"}, @{term "nr"}, $@{term "g"}^@{term "ny*nx"}$,
  declares the secret $@{term "g"}^@{term "ny*nx"}$
\item step 4: @{term "B"} receives the MAC insecurely,
  emits a commit signal for @{term "Resp"}, @{term "ni"}, @{term "nr"},
  $@{term "g"}^@{term "nx*ny"}$,
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
      progress := (progress s)(Ra \<mapsto> {xnx, xni, xgnx}),
      chan := {Confid A B (NonceF (Ra$ni))} \<union> 
             ({Insec A B (Exp Gen (NonceF (Ra$nx)))} \<union>
              (chan s))
      \<rparr>
  }"


definition
  l2_step2 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step2 Rb A B Ni gnx \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    Rb \<notin> dom (progress s) \<and>
    guessed_frame Rb xgnx = Some gnx \<and>
    guessed_frame Rb xni = Some Ni \<and>
    guessed_frame Rb xsk = Some (Exp gnx (NonceF (Rb$ny))) \<and>
    Confid A B Ni \<in> chan s \<and>
    Insec A B gnx \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Rb \<mapsto> {xny, xni, xnr, xgny, xgnx, xsk}),
            chan := {Confid B A (NonceF (Rb$nr))} \<union>
                   ({Insec B A 
                       \<langle>Exp Gen (NonceF (Rb$ny)),
                        hmac \<langle>Number 0, gnx, Exp Gen (NonceF (Rb$ny)), Agent B, Agent A\<rangle>
                             (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)\<rangle> } \<union> 
                    (chan s)),
            signalsInit := 
              if can_signal s A B then
                addSignal (signalsInit s) 
                          (Running A B \<langle>Ni, NonceF (Rb$nr), Exp gnx (NonceF (Rb$ny))\<rangle>)
              else
                signalsInit s,
            signalsInit2 := 
              if can_signal s A B then
                addSignal (signalsInit2 s) (Running A B (Exp gnx (NonceF (Rb$ny))))
              else
                signalsInit2 s
         \<rparr>
  }"  


definition
  l2_step3 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step3 Ra A B Nr gny \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    progress s Ra = Some {xnx, xni, xgnx} \<and>
    guessed_frame Ra xgny = Some gny \<and>
    guessed_frame Ra xnr = Some Nr \<and>
    guessed_frame Ra xsk = Some (Exp gny (NonceF (Ra$nx))) \<and>
    Confid B A Nr \<in> chan s \<and>
    Insec B A \<langle>gny, hmac \<langle>Number 0, Exp Gen (NonceF (Ra$nx)), gny, Agent B, Agent A\<rangle>
                         (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>)\<rangle> \<in> chan s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Ra \<mapsto> {xnx, xni, xnr, xgnx, xgny, xsk, xEnd}),
            chan := {Insec A B 
                       (hmac \<langle>Number 1, gny, Exp Gen (NonceF (Ra$nx)), Agent A, Agent B\<rangle>
                             (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>))} 
                    \<union> chan s,
            secret := {x. x = Exp gny (NonceF (Ra$nx)) \<and> Ra = test} \<union> secret s,
            signalsInit := 
              if can_signal s A B then
                addSignal (signalsInit s) 
                          (Commit A B \<langle>NonceF (Ra$ni), Nr, Exp gny (NonceF (Ra$nx))\<rangle>)
              else
                signalsInit s,
            signalsInit2 := 
              if can_signal s A B then
                addSignal (signalsInit2 s) (Commit A B (Exp gny (NonceF (Ra$nx))))
              else
                signalsInit2 s,
            signalsResp := 
              if can_signal s A B then
                addSignal (signalsResp s) 
                          (Running A B \<langle>NonceF (Ra$ni), Nr, Exp gny (NonceF (Ra$nx))\<rangle>)
              else
                signalsResp s,
            signalsResp2 := 
              if can_signal s A B then
                addSignal (signalsResp2 s) (Running A B (Exp gny (NonceF (Ra$nx))))
              else
                signalsResp2 s
          \<rparr>
  }"


definition
  l2_step4 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> msg \<Rightarrow> l2_trans"
where
  "l2_step4 Rb A B Ni gnx \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    progress s Rb = Some {xny, xni, xnr, xgnx, xgny, xsk} \<and>
    guessed_frame Rb xgnx = Some gnx \<and>
    guessed_frame Rb xni = Some Ni \<and>
    Insec A B (hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
                    (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)) \<in> chan s \<and>

    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Rb \<mapsto> {xny, xni, xnr, xgnx, xgny, xsk, xEnd}),
            secret := {x. x = Exp gnx (NonceF (Rb$ny)) \<and> Rb = test} \<union> secret s,
            signalsResp := 
              if can_signal s A B then
                addSignal (signalsResp s) 
                          (Commit A B \<langle>Ni, NonceF (Rb$nr), Exp gnx (NonceF (Rb$ny))\<rangle>)
              else
                signalsResp s,
            signalsResp2 := 
              if can_signal s A B then
                addSignal (signalsResp2 s) (Commit A B (Exp gnx (NonceF (Rb$ny))))
              else
                signalsResp2 s
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
    signalsInit = \<lambda>x. 0,
    signalsResp = \<lambda>x. 0,
    signalsInit2 = \<lambda>x. 0,
    signalsResp2 = \<lambda>x. 0,
    chan = {},
    bad = bad_init
    \<rparr>}"

definition 
  l2_trans :: "l2_trans" where
  "l2_trans \<equiv> (\<Union>m M X Rb Ra A B K Y.
     l2_step1 Ra A B \<union>
     l2_step2 Rb A B X Y \<union>
     l2_step3 Ra A B X Y \<union>
     l2_step4 Rb A B X Y \<union>
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
lemmas l2_step_defs = 
  l2_step1_def l2_step2_def l2_step3_def l2_step4_def 
  l2_dy_fake_chan_def l2_dy_fake_msg_def l2_lkr_after_def l2_lkr_others_def l2_skr_def

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

lemma in_progressS_trans: 
  "in_progressS (progress s R) S \<Longrightarrow> (s, s') \<in> trans l2 \<Longrightarrow> in_progressS (progress s' R) S" 
apply (auto simp add: l2_nostep_defs)
apply (auto simp add: l2_defs domIff)
done

(**************************************************************************************************)
subsection \<open>Invariants\<close>
(**************************************************************************************************)

subsubsection \<open>inv1\<close>
(**************************************************************************************************)

text \<open>If @{term "can_signal s A B"}
(i.e., @{term "A"}, @{term "B"} are the test session agents and the test 
is not finished), then @{term "A"}, @{term "B"} are honest.\<close>

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


subsubsection \<open>inv2\<close>
(**************************************************************************************************)

text \<open>For a run @{term "R"} (with any role), the session key is always
$something^n$ where $n$ is a nonce generated by @{term "R"}.\<close>

definition
  l2_inv2 :: "l2_state set"
where
  "l2_inv2 \<equiv> {s. \<forall>R.
    in_progress (progress s R) xsk \<longrightarrow>
    (\<exists> X N.
      guessed_frame R xsk = Some (Exp X (NonceF (R$N))))
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
apply (auto simp add: l2_defs dy_fake_chan_def dest: l2_inv2D)
done

lemma PO_l2_inv2 [iff]: "reach l2 \<subseteq> l2_inv2"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv3\<close>
(**************************************************************************************************)

definition
  "bad_runs s = {R. owner (guessed_runs R) \<in> bad s \<or> partner (guessed_runs R) \<in> bad s}"

abbreviation
  generators :: "l2_state \<Rightarrow> msg set"
where
  "generators s \<equiv> 
     \<comment> \<open>from the \<open>insec\<close> messages in steps 1 2\<close>
     {x. \<exists> N. x = Exp Gen (Nonce N)} \<union> 
     \<comment> \<open>from the opened \<open>confid\<close> messages in steps 1 2\<close>
     {x. \<exists> R \<in> bad_runs s. x = NonceF (R$ni) \<or> x = NonceF (R$nr)} \<union> 
     \<comment> \<open>from the \<open>insec\<close> messages in steps 2 3\<close>
     {x. \<exists> y y' z. x = hmac \<langle>y, y'\<rangle> (Hash z)} \<union> 
     \<comment> \<open>from the \<open>skr\<close>\<close>
     {Exp y (NonceF (R$N)) | y N R. R \<noteq> test \<and> R \<notin> partners}" 

lemma analz_generators: "analz (generators s) = generators s"
by (rule, rule, erule analz.induct) (auto)


definition 
  faked_chan_msgs :: "l2_state \<Rightarrow> chan set"
where
  "faked_chan_msgs s = 
     {Chan x A B M | x A B M. M \<in> synth (analz (extr (bad s) (ik s) (chan s)))}"
  
definition
  chan_generators :: "chan set"
where
  "chan_generators = {x. \<exists> n R. \<comment> \<open>the messages that can't be opened\<close>
     x = Confid (owner (guessed_runs R)) (partner (guessed_runs R)) (NonceF (R$n)) \<and> 
     (n = ni \<or> n = nr)
  }"


definition
  l2_inv3 :: "l2_state set"
where
  "l2_inv3 \<equiv> {s.
    extr (bad s) (ik s) (chan s) \<subseteq> synth (analz (generators s)) \<and>
    chan s \<subseteq> faked_chan_msgs s \<union> chan_generators
  }"
  
lemmas l2_inv3_aux_defs = faked_chan_msgs_def chan_generators_def
  
lemmas l2_inv3I = l2_inv3_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv3E = l2_inv3_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv3D = l2_inv3_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]
 
lemma l2_inv3_init [iff]:
  "init l2 \<subseteq> l2_inv3"
by (auto simp add: l2_def l2_init_def l2_inv3_def)

lemma l2_inv3_step1:
  "{l2_inv3} l2_step1 Ra A B {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv3I)
apply (auto simp add: l2_defs bad_runs_def intro: synth_analz_increasing dest!: l2_inv3D)
apply (auto simp add: l2_inv3_aux_defs intro: synth_analz_monotone 
            dest!: subsetD [where A="chan _"])
done

lemma l2_inv3_step2:
  "{l2_inv3} l2_step2 Rb A B Ni gnx {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv3I)
apply (auto simp add: l2_defs) 
apply (auto simp add: bad_runs_def intro: synth_analz_increasing dest!: l2_inv3D)
apply (auto simp add: l2_inv3_aux_defs)        \<comment> \<open>SLOW, ca. 30s\<close>
apply (blast intro: synth_analz_monotone analz.intros insert_iff synth_analz_increasing
             dest!: subsetD [where A="chan _"])+
done

lemma l2_inv3_step3:
  "{l2_inv3} l2_step3 Ra A B Nr gny {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv3I)
apply (auto simp add: l2_defs bad_runs_def intro: synth_analz_increasing dest!: l2_inv3D)
apply (auto simp add: l2_inv3_aux_defs)
apply (blast intro: synth_analz_monotone dest!: subsetD [where A="chan _"])+
done

lemma l2_inv3_step4:
  "{l2_inv3} l2_step4 Rb A B Ni gnx {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv3I, auto simp add: l2_defs)
apply (auto simp add: bad_runs_def intro:synth_analz_increasing dest!: l2_inv3D)
apply (auto simp add: l2_inv3_aux_defs dest!: subsetD [where A="chan _"])
done

lemma l2_inv3_dy_fake_msg:
  "{l2_inv3} l2_dy_fake_msg M {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_defs extr_insert_IK_eq 
            intro!: l2_inv3I 
            elim!: l2_inv3E dy_fake_msg_extr [THEN [2] rev_subsetD])
apply (auto intro!: fake_New
            intro: synth_analz_increasing fake_monotone dy_fake_msg_monotone 
                   dy_fake_msg_insert_chan  
            simp add: bad_runs_def elim!: l2_inv3E)
apply (auto simp add: l2_inv3_aux_defs intro: synth_analz_monotone 
            dest!: subsetD [where A="chan _"])
done


lemma l2_inv3_dy_fake_chan:
  "{l2_inv3} l2_dy_fake_chan M {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_defs 
            intro!: l2_inv3I 
            elim!: l2_inv3E)
apply (auto intro: synth_analz_increasing simp add: bad_runs_def elim!: l2_inv3E
            dest:dy_fake_msg_extr [THEN [2] rev_subsetD]
                 dy_fake_chan_extr_insert [THEN [2] rev_subsetD]
                 dy_fake_chan_mono2)
apply (simp add: l2_inv3_aux_defs dy_fake_chan_def dy_fake_msg_def, 
       erule fake.cases, simp_all)
apply (auto simp add: l2_inv3_aux_defs elim!: synth_analz_monotone 
            dest!: subsetD [where A="chan _"])
done

lemma l2_inv3_lkr_others:
  "{l2_inv3} l2_lkr_others A {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_defs 
            intro!: l2_inv3I
            dest!: extr_insert_bad [THEN [2] rev_subsetD]
            elim!: l2_inv3E)
apply (auto simp add: l2_inv3_aux_defs bad_runs_def 
            intro: synth_analz_increasing synth_analz_monotone)
apply (drule synth_analz_mono [where G="extr _ _ _"], auto,
       (drule rev_subsetD [where A="chan _"], simp)+, auto intro: synth_analz_increasing,
       drule rev_subsetD [where A="synth (analz (extr _ _ _))"], 
       auto intro: synth_analz_monotone)+
done

lemma l2_inv3_lkr_after:
  "{l2_inv3} l2_lkr_after A {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_defs intro!: l2_inv3I
            dest!: extr_insert_bad [THEN [2] rev_subsetD]
            elim!: l2_inv3E)
apply (auto simp add: l2_inv3_aux_defs bad_runs_def 
            intro: synth_analz_increasing synth_analz_monotone)
apply (drule synth_analz_mono [where G="extr _ _ _"], auto,
       (drule rev_subsetD [where A="chan _"], simp)+, auto intro: synth_analz_increasing,
       drule rev_subsetD [where A="synth (analz (extr _ _ _))"], 
       auto intro: synth_analz_monotone)+
done
 
lemma l2_inv3_skr:
  "{l2_inv3 \<inter> l2_inv2} l2_skr R K {> l2_inv3}"
apply (auto simp add: PO_hoare_defs l2_defs  intro!: l2_inv3I dest!: l2_inv2D)
apply (auto simp add: l2_inv3_aux_defs bad_runs_def intro: synth_analz_increasing   
            elim!: l2_inv3E)
apply (blast intro: synth_analz_monotone dest!: subsetD [where A="chan _"])+
done


lemmas l2_inv3_trans_aux =
  l2_inv3_step1 l2_inv3_step2 l2_inv3_step3 l2_inv3_step4
  l2_inv3_dy_fake_msg l2_inv3_dy_fake_chan
  l2_inv3_lkr_others l2_inv3_lkr_after l2_inv3_skr

lemma l2_inv3_trans [iff]:
  "{l2_inv3 \<inter> l2_inv2} trans l2 {> l2_inv3}"
by (auto simp add: l2_nostep_defs intro:l2_inv3_trans_aux)

lemma PO_l2_inv3 [iff]: "reach l2 \<subseteq> l2_inv3"
by (rule_tac J="l2_inv2" in inv_rule_incr) (auto)

text \<open>Auxiliary dest rule for inv3.\<close>

lemmas l2_inv3D_aux =
  l2_inv3D [THEN conjunct1,
            THEN [2] subset_trans,
            THEN synth_analz_mono, simplified,
            THEN [2] rev_subsetD, rotated 1, OF IK_subset_extr]

lemma l2_inv3D_HashNonce1:
  "s \<in> l2_inv3 \<Longrightarrow>
   Hash \<langle>NonceF (R$N), X\<rangle> \<in> synth (analz (extr (bad s) (ik s) (chan s))) \<Longrightarrow>
   R \<in> bad_runs s"
apply (drule l2_inv3D, auto, drule synth_analz_monotone, auto simp add: analz_generators)
apply (erule synth.cases, auto)
done

lemma l2_inv3D_HashNonce2:
  "s \<in> l2_inv3 \<Longrightarrow>
   Hash \<langle>X, NonceF (R$N)\<rangle> \<in> synth (analz (extr (bad s) (ik s) (chan s))) \<Longrightarrow>
   R \<in> bad_runs s"
apply (drule l2_inv3D, auto, drule synth_analz_monotone, auto simp add: analz_generators)
apply (erule synth.cases, auto)
done



subsubsection \<open>hmac preservation lemmas\<close>
(**************************************************************************************************)

text \<open>If @{term "(s, s') \<in> trans l2"} then the MACs (with secret keys) that the attacker knows in
  @{term "s'"} (overapproximated by those in @{term "parts (extr (bad s') (ik s') (chan s'))"})
  are already known in @{term "s"}, except in the case of the steps 2 and 3 of the protocol.
\<close>

lemma hmac_key_unknown:
  "hmac X K \<in> synth (analz H) \<Longrightarrow> K \<notin> synth (analz H) \<Longrightarrow> hmac X K \<in> analz H"
by (erule synth.cases, auto)

lemma parts_exp [simp]:"parts {Exp X Y} = {Exp X Y}"
by (auto,erule parts.induct, auto)

lemma hmac_trans_1_4_skr_extr_fake:
  "hmac X K \<in> parts (extr (bad s') (ik s') (chan s')) \<Longrightarrow>
   K \<notin> synth (analz (extr (bad s) (ik s) (chan s))) \<Longrightarrow> \<comment> \<open>necessary for the \<open>dy_fake_msg\<close> case\<close>
   s \<in> l2_inv2 \<Longrightarrow> \<comment> \<open>necessary for the \<open>skr\<close> case\<close>
   (s, s') \<in> l2_step1 Ra A B \<union> l2_step4 Rb A B Ni gnx \<union> l2_skr R KK \<union> 
             l2_dy_fake_msg M \<union> l2_dy_fake_chan MM \<Longrightarrow>
     hmac X K \<in> parts (extr (bad s) (ik s) (chan s))"
apply (auto simp add: l2_defs parts_insert [where H="extr _ _ _"] 
                              parts_insert [where H="insert _ (extr _ _ _)"])
apply (auto dest!:l2_inv2D)
apply (auto dest!:dy_fake_chan_extr_insert_parts [THEN [2] rev_subsetD]
                  parts_monotone [of _ "{M}" "synth (analz (extr (bad s) (ik s) (chan s)))"],
       auto simp add: dy_fake_msg_def)
done

lemma hmac_trans_2:
  "hmac X K \<in> parts (extr (bad s') (ik s') (chan s')) \<Longrightarrow>
   (s, s') \<in> l2_step2 Rb A B Ni gnx \<Longrightarrow>
   hmac X K \<in> parts (extr (bad s) (ik s) (chan s)) \<or>
   (X = \<langle>Number 0, gnx, Exp Gen (NonceF (Rb$ny)), Agent B, Agent A\<rangle> \<and>
    K = Hash \<langle>Ni, NonceF (Rb$nr)\<rangle> \<and>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    progress s' Rb = Some {xny, xni, xnr, xgnx, xgny, xsk} \<and>
    guessed_frame Rb xgnx = Some gnx \<and>
    guessed_frame Rb xni = Some Ni )"
apply (auto simp add: l2_defs parts_insert [where H="extr _ _ _"] 
                              parts_insert [where H="insert _ (extr _ _ _)"])
done

lemma hmac_trans_3:
  "hmac X K \<in> parts (extr (bad s') (ik s') (chan s')) \<Longrightarrow>
   (s, s') \<in> l2_step3 Ra A B Nr gny \<Longrightarrow>
   hmac X K \<in> parts (extr (bad s) (ik s) (chan s)) \<or>
   (X = \<langle>Number 1, gny, Exp Gen (NonceF (Ra$nx)), Agent A, Agent B\<rangle> \<and>
    K = Hash \<langle>NonceF (Ra$ni), Nr\<rangle> \<and>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    progress s' Ra = Some {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
    guessed_frame Ra xgny = Some gny \<and>
    guessed_frame Ra xnr = Some Nr)"
apply (auto simp add: l2_defs parts_insert [where H="extr _ _ _"] 
                              parts_insert [where H="insert _ (extr _ _ _)"])
done

lemma hmac_trans_lkr_aux:
  "hmac X K \<in> parts {M. \<exists> x A B. Chan x A B M \<in> chan s} \<Longrightarrow>
   K \<notin> synth (analz (extr (bad s) (ik s) (chan s))) \<Longrightarrow>
   s \<in> l2_inv3 \<Longrightarrow>
   hmac X K \<in> parts (extr (bad s) (ik s) (chan s))"
proof -
  assume A:"K \<notin> synth (analz (extr (bad s) (ik s) (chan s)))" "s \<in> l2_inv3"
  assume "hmac X K \<in> parts {M. \<exists> x A B. Chan x A B M \<in> chan s}"
  then obtain x A B M where H:"hmac X K \<in> parts {M}" and H':"Chan x A B M \<in> chan s"
    by (auto dest: parts_singleton)
  assume "s \<in> l2_inv3"
  with H' have "M \<in> range Nonce  \<or> M \<in> synth (analz (extr (bad s) (ik s) (chan s)))"
    by (auto simp add: l2_inv3_aux_defs dest!: l2_inv3D, auto)
  with H show ?thesis
    proof (auto)
      assume "M \<in> synth (analz (extr (bad s) (ik s) (chan s)))"
      then have "{M} \<subseteq> synth (analz (extr (bad s) (ik s) (chan s)))" by (auto)
      then have "parts {M} \<subseteq> parts (synth (analz (extr (bad s) (ik s) (chan s))))" 
        by (rule parts_mono)
      with H have "hmac X K \<in> parts (synth (analz (extr (bad s) (ik s) (chan s))))" by auto
      with A show ?thesis by auto
    qed
qed
 

lemma hmac_trans_lkr:
  "hmac X K \<in> parts (extr (bad s') (ik s') (chan s')) \<Longrightarrow>
   K \<notin> synth (analz (extr (bad s) (ik s) (chan s))) \<Longrightarrow>
   s \<in> l2_inv3 \<Longrightarrow> 
   (s, s') \<in> l2_lkr_others A \<union> l2_lkr_after A \<Longrightarrow>
   hmac X K \<in> parts (extr (bad s) (ik s) (chan s))"
apply (auto simp add: l2_defs
            dest!: parts_monotone [OF _ extr_insert_bad])
apply (auto intro: parts_monotone intro!:hmac_trans_lkr_aux)
done

lemmas hmac_trans = hmac_trans_1_4_skr_extr_fake hmac_trans_lkr hmac_trans_2 hmac_trans_3



subsubsection \<open>inv4 (authentication guard)\<close>
(**************************************************************************************************)

text \<open>If HMAC is @{term "parts (extr (bad s) (ik s) (chan s))"} and @{term "A"}, @{term "B"} 
are honest then the message has indeed been sent by a responder run (etc).\<close>

definition
  l2_inv4 :: "l2_state set"
where
  "l2_inv4 \<equiv> {s. \<forall> Ra A B gny Nr.
     hmac \<langle>Number 0, Exp Gen (NonceF (Ra$nx)), gny, Agent B, Agent A\<rangle>
        (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>) \<in> parts (extr (bad s) (ik s) (chan s)) \<longrightarrow>
     guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<longrightarrow>
     A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
      (\<exists> Rb. guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
             in_progressS (progress s Rb) {xny, xni, xnr, xgnx, xgny, xsk} \<and>
             guessed_frame Rb xgny = Some gny \<and>
             guessed_frame Rb xnr = Some Nr \<and>
             guessed_frame Rb xni = Some (NonceF (Ra$ni)) \<and>
             guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))))
    }"

lemmas l2_inv4I = l2_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv4E [elim] = l2_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv4D = l2_inv4_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv4_init [iff]:
  "init l2 \<subseteq> l2_inv4"
by (auto simp add: l2_def l2_init_def l2_inv4_def)

lemma l2_inv4_trans [iff]:
  "{l2_inv4 \<inter> l2_inv2 \<inter> l2_inv3} trans l2 {> l2_inv4}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv4I)
  fix s' s :: l2_state
  fix Ra A B gny Nr
  assume HHparts:"hmac \<langle>Number 0, Exp Gen (NonceF (Ra $ nx)), gny, Agent B, Agent A\<rangle>
             (Hash \<langle>NonceF (Ra $ ni), Nr\<rangle>)
       \<in> parts (extr (bad s') (ik s') (chan s'))"
  assume HRa: "guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
  assume Hi:"s \<in> l2_inv4" "s \<in> l2_inv2" "s \<in> l2_inv3"
  assume Ht:"(s, s') \<in> trans l2"
  assume "A \<notin> bad s'" "B \<notin> bad s'"
  with Ht have Hb:"A \<notin> bad s" "B \<notin> bad s" 
    by (auto simp add: l2_nostep_defs) (simp_all add: l2_defs)
  with HRa Hi 
  have HH:"Hash \<langle>NonceF (Ra$ ni),  Nr\<rangle> \<notin> synth (analz (extr (bad s) (ik s) (chan s)))"
    by (auto dest!: l2_inv3D_HashNonce1 simp add: bad_runs_def)
  from Ht Hi HHparts HH 
  have "hmac \<langle>Number 0, Exp Gen (NonceF (Ra $ nx)), gny, Agent B, Agent A\<rangle>
             (Hash \<langle>NonceF (Ra $ ni), Nr\<rangle>) \<in> parts (extr (bad s) (ik s) (chan s)) \<or>
        (\<exists> Rb. (s, s') \<in> l2_step2 Rb A B (NonceF (Ra$ni)) (Exp Gen (NonceF (Ra $ nx))) \<and>
               gny = Exp Gen (NonceF (Rb$ny)) \<and>
               Nr = NonceF (Rb$nr) \<and>
               guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
               progress s' Rb = Some {xny, xni, xnr, xgnx, xgny, xsk} \<and>
               guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))) \<and>
               guessed_frame Rb xni = Some (NonceF (Ra$ni)))"
    apply (auto simp add: l2_nostep_defs)
    (*apply (auto dest: hmac_trans) does not work*)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_2, auto)
    apply (drule hmac_trans_3, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_lkr, auto)
    apply (drule hmac_trans_lkr, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    done
  then show "\<exists>Rb. guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr> \<and>
            in_progressS (progress s' Rb) {xny, xni, xnr, xgnx, xgny, xsk} \<and>
            guessed_frame Rb xgny = Some gny \<and>
            guessed_frame Rb xnr = Some Nr \<and>
            guessed_frame Rb xni = Some (NonceF (Ra $ ni)) \<and>
            guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra $ nx)))"
     proof (auto)
       assume 
         "hmac \<langle>Number 0, Exp Gen (NonceF (Ra $ nx)), gny, Agent B, Agent A\<rangle> 
               (hmac (NonceF (Ra $ ni)) Nr)
            \<in> parts (extr (bad s) (ik s) (chan s))"
       with Hi Hb HRa obtain Rb where 
         HRb: "guessed_runs Rb = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
              "in_progressS (progress s Rb) {xny, xni, xnr, xgnx, xgny, xsk}"
              "guessed_frame Rb xgny = Some gny"
              "guessed_frame Rb xnr = Some Nr"
              "guessed_frame Rb xni = Some (NonceF (Ra $ ni))"
              "guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra $ nx)))"
         by (auto dest!: l2_inv4D)
       with Ht have "in_progressS (progress s' Rb) {xny, xni, xnr, xgnx, xgny, xsk}"
         by (auto elim: in_progressS_trans)
       with HRb show ?thesis by auto
     qed
qed

lemma PO_l2_inv4 [iff]: "reach l2 \<subseteq> l2_inv4"
by (rule_tac J="l2_inv2 \<inter> l2_inv3" in inv_rule_incr) (auto)


lemma auth_guard_step3:
  "s \<in> l2_inv4 \<Longrightarrow>
   s \<in> l2_inv1 \<Longrightarrow>
   Insec B A \<langle>gny, hmac \<langle>Number 0, Exp Gen (NonceF (Ra$nx)), gny, Agent B, Agent A\<rangle>
                        (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>)\<rangle>
     \<in> chan s \<Longrightarrow>
   guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<Longrightarrow>
   can_signal s A B \<Longrightarrow>
   (\<exists> Rb. guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
      in_progressS (progress s Rb) {xny, xni, xnr, xgnx, xgny, xsk} \<and>
      guessed_frame Rb xgny = Some gny \<and>
      guessed_frame Rb xnr = Some Nr \<and>
      guessed_frame Rb xni = Some (NonceF (Ra$ni)) \<and>
      guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))))"
proof -
  assume "s \<in> l2_inv1" "can_signal s A B"
  hence Hb:"A \<notin> bad s" "B \<notin> bad s" by auto
  assume "Insec B A \<langle>gny, hmac \<langle>Number 0, Exp Gen (NonceF (Ra$nx)), gny, Agent B, Agent A\<rangle>
                        (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>)\<rangle> \<in> chan s"
  hence HH:
    "hmac \<langle>Number 0, Exp Gen (NonceF (Ra$nx)), gny, Agent B, Agent A\<rangle> 
          (Hash \<langle>NonceF (Ra$ni), Nr\<rangle>)
       \<in> parts (extr (bad s) (ik s) (chan s))" by auto
  assume "s \<in> l2_inv4" "guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
  with Hb HH show ?thesis by auto
qed


subsubsection \<open>inv5 (authentication guard)\<close>
(**************************************************************************************************)

text \<open>If MAC is in @{term "parts (extr (bad s) (ik s) (chan s))"} and @{term "A"}, @{term "B"}
  are honest then the message has indeed been sent by an initiator run (etc).\<close>

definition
  l2_inv5 :: "l2_state set"
where
  "l2_inv5 \<equiv> {s. \<forall> Rb A B gnx Ni.
     hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
        (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>) \<in> parts (extr (bad s) (ik s) (chan s)) \<longrightarrow>
     guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<longrightarrow>
     A \<notin> bad s \<and> B \<notin> bad s \<longrightarrow>
      (\<exists> Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
             in_progressS (progress s Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
             guessed_frame Ra xgnx = Some gnx \<and>
             guessed_frame Ra xni = Some Ni \<and>
             guessed_frame Ra xnr = Some (NonceF (Rb$nr)) \<and>
             guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))))
    }"

lemmas l2_inv5I = l2_inv5_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv5E [elim] = l2_inv5_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv5D = l2_inv5_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv5_init [iff]:
  "init l2 \<subseteq> l2_inv5"
by (auto simp add: l2_def l2_init_def l2_inv5_def)

lemma l2_inv5_trans [iff]:
  "{l2_inv5 \<inter> l2_inv2 \<inter> l2_inv3} trans l2 {> l2_inv5}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv5I)
  fix s' s :: l2_state
  fix Rb A B gnx Ni
  assume HHparts:"hmac \<langle>Number (Suc 0), Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
             (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)
       \<in> parts (extr (bad s') (ik s') (chan s'))"
  assume HRb: "guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr>"
  assume Hi:"s \<in> l2_inv5" "s \<in> l2_inv2" "s \<in> l2_inv3"
  assume Ht:"(s, s') \<in> trans l2"
  assume "A \<notin> bad s'" "B \<notin> bad s'"
  with Ht have Hb:"A \<notin> bad s" "B \<notin> bad s" 
    by (auto simp add: l2_nostep_defs) (simp_all add: l2_defs)
  with HRb Hi have HH:"Hash \<langle>Ni, NonceF (Rb$nr)\<rangle> \<notin> synth (analz (extr (bad s) (ik s) (chan s)))"
    by (auto dest!: l2_inv3D_HashNonce2 simp add: bad_runs_def)
  from Ht Hi HHparts HH have "hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
             (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>) \<in> parts (extr (bad s) (ik s) (chan s)) \<or>
        (\<exists> Ra. (s, s') \<in> l2_step3 Ra A B (NonceF (Rb$nr)) (Exp Gen (NonceF (Rb$ny))) \<and>
               gnx = Exp Gen (NonceF (Ra$nx)) \<and>
               Ni = NonceF (Ra$ni) \<and>
               guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
               progress s' Ra = Some {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
               guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))) \<and>
               guessed_frame Ra xnr = Some (NonceF (Rb$nr)))"
    apply (auto simp add: l2_nostep_defs)
    (*apply (auto dest: hmac_trans) does not work*)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_2, auto)
    apply (drule hmac_trans_3, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    apply (drule hmac_trans_lkr, auto)
    apply (drule hmac_trans_lkr, auto)
    apply (drule hmac_trans_1_4_skr_extr_fake, auto)
    done
  then show "\<exists>Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
            in_progressS (progress s' Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
            guessed_frame Ra xgnx = Some gnx \<and>
            guessed_frame Ra xni = Some Ni \<and>
            guessed_frame Ra xnr = Some (NonceF (Rb$nr)) \<and>
            guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny)))"
     proof (auto)
       assume 
         "hmac \<langle>Number (Suc 0), Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle> 
               (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)
            \<in> parts (extr (bad s) (ik s) (chan s))"
       with Hi Hb HRb obtain Ra where HRa:"guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
            "in_progressS (progress s Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd}"
            "guessed_frame Ra xgnx = Some gnx"
            "guessed_frame Ra xni = Some Ni"
            "guessed_frame Ra xnr = Some (NonceF (Rb$nr))"
            "guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny)))"
         by (auto dest!: l2_inv5D)
       with Ht have "in_progressS (progress s' Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd}"
         by (auto elim: in_progressS_trans)
       with HRa show ?thesis by auto
     qed
qed

lemma PO_l2_inv5 [iff]: "reach l2 \<subseteq> l2_inv5"
by (rule_tac J="l2_inv2 \<inter> l2_inv3" in inv_rule_incr) (auto)


lemma auth_guard_step4:
  "s \<in> l2_inv5 \<Longrightarrow>
   s \<in> l2_inv1 \<Longrightarrow>
   Insec A B (hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
                        (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>))
     \<in> chan s \<Longrightarrow>
   guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<Longrightarrow>
   can_signal s A B \<Longrightarrow>
   (\<exists> Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
      in_progressS (progress s Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
      guessed_frame Ra xgnx = Some gnx \<and>
      guessed_frame Ra xni = Some Ni \<and>
      guessed_frame Ra xnr = Some (NonceF (Rb$nr)) \<and>
      guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))))"
proof -
  assume "s \<in> l2_inv1" "can_signal s A B"
  hence Hb:"A \<notin> bad s" "B \<notin> bad s" by auto
  assume "Insec A B (hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle>
                        (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)) \<in> chan s"
  hence HH:
    "hmac \<langle>Number 1, Exp Gen (NonceF (Rb$ny)), gnx, Agent A, Agent B\<rangle> 
          (Hash \<langle>Ni, NonceF (Rb$nr)\<rangle>)
       \<in> parts (extr (bad s) (ik s) (chan s))" by auto
  assume "s \<in> l2_inv5" "guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr>"
  with Hb HH show ?thesis by auto
qed


subsubsection \<open>inv6\<close>
(**************************************************************************************************)

text \<open>For an initiator, the session key is always $@{term "gny"}^@{term "nx"}$.\<close>

definition
  l2_inv6 :: "l2_state set"
where
  "l2_inv6 \<equiv> {s. \<forall>Ra A B gny.
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<longrightarrow>
    in_progress (progress s Ra) xsk \<longrightarrow>
    guessed_frame Ra xgny = Some gny \<longrightarrow>
    guessed_frame Ra xsk = Some (Exp gny (NonceF (Ra$nx)))
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
apply (auto simp add: l2_defs dy_fake_chan_def)
done

lemma PO_l2_inv6 [iff]: "reach l2 \<subseteq> l2_inv6"
by (rule inv_rule_basic) (auto)


subsubsection \<open>inv6'\<close>
(**************************************************************************************************)

text \<open>For a responder, the session key is always $@{term "gnx"}^@{term "ny"}$.\<close>

definition
  l2_inv6' :: "l2_state set"
where
  "l2_inv6' \<equiv> {s. \<forall>Rb A B gnx.
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<longrightarrow>
    in_progress (progress s Rb) xsk \<longrightarrow>
    guessed_frame Rb xgnx = Some gnx \<longrightarrow>
    guessed_frame Rb xsk = Some (Exp gnx (NonceF (Rb$ny)))
  }"

lemmas l2_inv6'I = l2_inv6'_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv6'E [elim] = l2_inv6'_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv6'D = l2_inv6'_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv6'_init [iff]:
  "init l2 \<subseteq> l2_inv6'"
by (auto simp add: l2_def l2_init_def l2_inv6'_def)

lemma l2_inv6'_trans [iff]:
  "{l2_inv6'} trans l2 {> l2_inv6'}"
apply (auto simp add: PO_hoare_defs l2_nostep_defs intro!: l2_inv6'I)
apply (auto simp add: l2_defs dy_fake_chan_def)
done

lemma PO_l2_inv6' [iff]: "reach l2 \<subseteq> l2_inv6'"
by (rule inv_rule_basic) (auto)

subsubsection \<open>inv7: form of the secrets\<close>
(**************************************************************************************************)
definition
  l2_inv7 :: "l2_state set"
where
  "l2_inv7 \<equiv> {s.
    secret s \<subseteq> {Exp (Exp Gen (NonceF (R$N))) (NonceF (R'$N')) | N N' R R'.
                  R = test \<and> R' \<in> partners \<and> (N=nx \<or> N=ny) \<and> (N'=nx \<or> N'=ny)}
  }"

lemmas l2_inv7I = l2_inv7_def [THEN setc_def_to_intro, rule_format]
lemmas l2_inv7E [elim] = l2_inv7_def [THEN setc_def_to_elim, rule_format]
lemmas l2_inv7D = l2_inv7_def [THEN setc_def_to_dest, rule_format, rotated 1, simplified]

lemma l2_inv7_init [iff]:
  "init l2 \<subseteq> l2_inv7"
by (auto simp add: l2_def l2_init_def l2_inv7_def)


text \<open>Steps 3 and 4 are the hard part.\<close>

lemma l2_inv7_step3:
  "{l2_inv7 \<inter> l2_inv1 \<inter> l2_inv4 \<inter> l2_inv6'} l2_step3 Ra A B Nr gny {> l2_inv7}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv7I)
  fix s s' :: l2_state fix x
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv7" "s \<in> l2_inv4" "s \<in> l2_inv6'"
  assume Ht:"(s, s') \<in> l2_step3 Ra A B Nr gny"
  assume Hs:"x \<in> secret s'"
  from Hs Ht have "x \<in> secret s \<or> (Ra = test \<and> x = Exp gny (NonceF (Ra$nx)))"
    by (auto simp add: l2_defs)
  with Hi Ht 
  show "\<exists>N N' R'. x = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and> 
                  R' \<in> partners \<and> (N = nx \<or> N = ny) \<and> (N' = nx \<or> N' = ny)"
    proof (auto dest: l2_inv7D simp add: l2_defs)
      assume Htest: "guessed_runs test = \<lparr>role = Init, owner = A, partner = B\<rparr>"
                    "guessed_frame test xgny = Some gny"
                    "guessed_frame test xnr = Some Nr"
                    "guessed_frame test xsk = Some (Exp gny (NonceF (test $ nx)))"
      assume 
        "Insec B A \<langle>gny, hmac \<langle>Number 0, Exp Gen (NonceF (test$nx)), gny, Agent B, Agent A\<rangle>
                              (Hash \<langle>NonceF (test$ni), Nr\<rangle>)\<rangle>
                  \<in> chan s"
        "can_signal s A B"
      with Htest Hi obtain Rb where HRb:
        "guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr>"
        "in_progressS (progress s Rb) {xny, xni, xnr, xgnx, xgny, xsk}"
        "gny = Exp Gen (NonceF (Rb$ny))"
        "Nr = NonceF (Rb$nr)"
        "guessed_frame Rb xni = Some (NonceF (test$ni))"
        "guessed_frame Rb xgnx = Some (Exp Gen (NonceF (test$nx)))"
        by (auto dest!: auth_guard_step3)
      with Hi 
      have "guessed_frame Rb xsk = Some (Exp (Exp Gen (NonceF (Rb$ny))) (NonceF (test$nx)))"
        by (auto dest: l2_inv6'D)
      with HRb Htest have "Rb \<in> partners"
        by (auto simp add: partners_def partner_runs_def, simp add: matching_def)
      with HRb have "Exp gny (NonceF (test $ nx)) = 
                        Exp (Exp Gen (NonceF (Rb $ ny))) (NonceF (test $ nx)) \<and> Rb \<in> partners"
        by auto
      then show "\<exists>N N' R'.
          Exp gny (NonceF (test $ nx)) = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and>
          R' \<in> partners \<and> (N = nx \<or> N = ny) \<and> (N' = nx \<or> N' = ny)"
        by blast
    qed (auto simp add: can_signal_def)
qed

lemma l2_inv7_step4:
  "{l2_inv7 \<inter> l2_inv1 \<inter> l2_inv5 \<inter> l2_inv6 \<inter> l2_inv6'} l2_step4 Rb A B Ni gnx {> l2_inv7}"
proof (auto simp add: PO_hoare_defs intro!: l2_inv7I)
  fix s s' :: l2_state fix x
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv7" "s \<in> l2_inv5" "s \<in> l2_inv6" "s \<in> l2_inv6'"
  assume Ht:"(s, s') \<in> l2_step4 Rb A B Ni gnx"
  assume Hs:"x \<in> secret s'"
  from Hs Ht have "x \<in> secret s \<or> (Rb = test \<and> x = Exp gnx (NonceF (Rb$ny)))"
    by (auto simp add: l2_defs)
  with Hi Ht 
  show "\<exists>N N' R'. x = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and> R' \<in> partners
                                \<and> (N = nx \<or> N = ny) \<and> (N' = nx \<or> N' = ny)"
    proof (auto dest: l2_inv7D simp add: l2_defs)
      assume Htest: "guessed_runs test = \<lparr>role = Resp, owner = B, partner = A\<rparr>"
                    "guessed_frame test xgnx = Some gnx"
                    "guessed_frame test xni = Some Ni"
      assume "progress s test = Some {xny, xni, xnr, xgnx, xgny, xsk}"
      with Htest Hi have Htest': "guessed_frame test xsk = Some (Exp gnx (NonceF (test $ ny)))"
        by (auto dest: l2_inv6'D)
      assume 
        "Insec A B (hmac \<langle>Number (Suc 0), Exp Gen (NonceF (test$ny)), gnx, Agent A, Agent B\<rangle>
                         (Hash \<langle>Ni, NonceF (test $ nr)\<rangle>))
            \<in> chan s"
        "can_signal s A B"
      with Hi Htest obtain Ra where HRa:
        "guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr>"
        "in_progressS (progress s Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd}"
        "gnx = Exp Gen (NonceF (Ra$nx))"
        "Ni = NonceF (Ra$ni)"
        "guessed_frame Ra xgny = Some (Exp Gen (NonceF (test$ny)))"
        "guessed_frame Ra xnr = Some (NonceF (test$nr))"
        by (auto dest!: auth_guard_step4)
      with Hi 
      have "guessed_frame Ra xsk = Some (Exp (Exp Gen (NonceF (Ra$nx))) (NonceF (test$ny)))"
        by (auto dest: l2_inv6D)
      with HRa Htest Htest' have "Ra \<in> partners"
        by (auto simp add: partners_def partner_runs_def, simp add: matching_def)
      with HRa have "Exp gnx (NonceF (test $ ny)) = 
                        Exp (Exp Gen (NonceF (Ra $ nx))) (NonceF (test $ ny)) \<and> Ra \<in> partners"
        by auto
      then show "\<exists>N N' R'.
          Exp gnx (NonceF (test $ ny)) 
          = Exp (Exp Gen (NonceF (R' $ N'))) (NonceF (test $ N)) \<and>
          R' \<in> partners \<and> (N = nx \<or> N = ny) \<and> (N' = nx \<or> N' = ny)"
        by auto
    qed (auto simp add: can_signal_def)
qed


lemma l2_inv7_trans [iff]:
  "{l2_inv7 \<inter> l2_inv1 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> l2_inv6 \<inter> l2_inv6'} trans l2 {> l2_inv7}"
apply (auto simp add: l2_nostep_defs intro!: l2_inv7_step3 l2_inv7_step4)
apply (auto simp add: PO_hoare_defs intro!: l2_inv7I)
apply (auto simp add: l2_defs dy_fake_chan_def dest: l2_inv7D)
done

lemma PO_l2_inv7 [iff]: "reach l2 \<subseteq> l2_inv7"
by (rule_tac J="l2_inv1 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> l2_inv6 \<inter> l2_inv6'" in inv_rule_incr) (auto)


text \<open>auxiliary dest rule for inv7\<close>
lemma Exp_Exp_Gen_synth: 
"Exp (Exp Gen X) Y \<in> synth H \<Longrightarrow> Exp (Exp Gen X) Y \<in> H \<or> X \<in> synth H \<or> Y \<in> synth H"
by (erule synth.cases, auto dest: Exp_Exp_Gen_inj2)

lemma l2_inv7_aux:
  "s \<in> l2_inv7 \<Longrightarrow>
   x \<in> secret s \<Longrightarrow>
   x \<notin> synth (analz (generators s))"
apply (auto simp add: analz_generators dest!: l2_inv7D [THEN [2] rev_subsetD])
apply (auto dest!: Exp_Exp_Gen_synth Exp_Exp_Gen_inj2)
done

(**************************************************************************************************)
subsection \<open>Refinement\<close>
(**************************************************************************************************)

text \<open>Mediator function.\<close>

definition
  med12s :: "l2_obs \<Rightarrow> skl1_obs"
where
  "med12s t \<equiv> \<lparr>
    ik = ik t,
    secret = secret t,
    progress = progress t,
    signalsInit = signalsInit t,
    signalsResp = signalsResp t,
    signalsInit2 = signalsInit2 t,
    signalsResp2 = signalsResp2 t
    \<rparr>"


text \<open>Relation between states.\<close>
definition
  R12s :: "(skl1_state * l2_state) set"
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
  "{R12s} skl1_step1 Ra A B, l2_step1 Ra A B {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs skl1_step1_def l2_step1_def)

lemma l2_step2_refines_step2:
  "{R12s} skl1_step2 Rb A B Ni gnx, l2_step2 Rb A B Ni gnx {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs skl1_step2_def, simp_all add: l2_step2_def)

text \<open>for step3 and 4, we prove the level 1 guard, i.e.,
  "the future session key is not in @{term "synth (analz (ik s))"}",
  using the fact that inv8 also holds for the future state in which the session key is already in 
  @{term "secret s"}\<close>
lemma l2_step3_refines_step3:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv6' \<inter> l2_inv7)} 
      skl1_step3 Ra A B Nr gny, l2_step3 Ra A B Nr gny 
   {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs)
  fix s s'
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv4" "s\<in> l2_inv6'"
  assume Ht: "(s, s') \<in> l2_step3 Ra A B Nr gny"
  assume "s \<in> l2_inv7" "s \<in> l2_inv3"
  with Hi Ht l2_inv7_step3 l2_inv3_step3 have Hi':"s' \<in> l2_inv7" "s'\<in> l2_inv3"
    by (auto simp add: PO_hoare_defs, blast, blast)
  from Ht have "Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<in> secret s'"
    by (auto simp add: l2_defs)
  with Hi' have "Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<notin> synth (analz (generators s'))"
    by (auto dest: l2_inv7_aux)
  with Hi' have G2:"Ra = test \<longrightarrow> Exp gny (NonceF (Ra$nx)) \<notin> synth (analz (ik s'))"
    by (auto dest!: l2_inv3D_aux)
  from Ht Hi have G1:
    "can_signal s A B \<longrightarrow> (\<exists> Rb. guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
           in_progressS (progress s Rb) {xny, xni, xnr, xgnx, xgny, xsk} \<and>
           gny = Exp Gen (NonceF (Rb$ny)) \<and>
           Nr = NonceF (Rb$nr) \<and>
           guessed_frame Rb xgnx = Some (Exp Gen (NonceF (Ra$nx))) \<and>
           guessed_frame Rb xni = Some (NonceF (Ra$ni)))"
   by (auto dest!: auth_guard_step3 simp add: l2_defs)
  with Ht G1 G2 show
    "(\<lparr>ik = ik s, secret = secret s, progress = progress s, 
       signalsInit = signalsInit s, signalsResp = signalsResp s,
       signalsInit2 = signalsInit2 s, signalsResp2 = signalsResp2 s\<rparr>,
      \<lparr>ik = ik s', secret = secret s', progress = progress s',
       signalsInit = signalsInit s', signalsResp = signalsResp s',
       signalsInit2 = signalsInit2 s', signalsResp2 = signalsResp2 s'\<rparr>)
           \<in> skl1_step3 Ra A B Nr gny"
    apply (auto simp add: l2_step3_def, auto simp add: skl1_step3_def)
    apply (auto simp add: can_signal_def)
    done
qed

lemma l2_step4_refines_step4:
  "{R12s \<inter> UNIV \<times> (l2_inv1 \<inter> l2_inv3 \<inter> l2_inv5 \<inter> l2_inv6 \<inter> l2_inv6' \<inter> l2_inv7)} 
      skl1_step4 Rb A B Ni gnx, l2_step4 Rb A B Ni gnx
   {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs)
  fix s s'
  assume Hi:"s \<in> l2_inv1" "s \<in> l2_inv5" "s \<in> l2_inv6" "s \<in> l2_inv6'"
  assume Ht: "(s, s') \<in> l2_step4 Rb A B Ni gnx"
  assume "s \<in> l2_inv7" "s \<in> l2_inv3"
  with Hi Ht l2_inv7_step4 l2_inv3_step4 have Hi':"s' \<in> l2_inv7" "s' \<in> l2_inv3"
    by (auto simp add: PO_hoare_defs, blast, blast)
  from Ht have "Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<in> secret s'"
    by (auto simp add: l2_defs)
  with Hi' have "Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<notin> synth (analz (generators s'))"
    by (auto dest: l2_inv7_aux)
  with Hi' have G2:"Rb = test \<longrightarrow> Exp gnx (NonceF (Rb$ny)) \<notin> synth (analz (ik s'))"
    by (auto dest!: l2_inv3D_aux)
  from Ht Hi have G1:
    "can_signal s A B \<longrightarrow> (\<exists> Ra. guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
              in_progressS (progress s Ra) {xnx, xni, xnr, xgnx, xgny, xsk, xEnd} \<and>
              guessed_frame Ra xgnx = Some gnx \<and>
              guessed_frame Ra xni = Some Ni \<and>
              guessed_frame Ra xgny = Some (Exp Gen (NonceF (Rb$ny))) \<and>
              guessed_frame Ra xnr = Some (NonceF (Rb$nr)))"
   by (auto dest!: auth_guard_step4 simp add: l2_defs)
  with Ht G1 G2 show
    "(\<lparr>ik = ik s, secret = secret s, progress = progress s,
       signalsInit = signalsInit s, signalsResp = signalsResp s,
       signalsInit2 = signalsInit2 s, signalsResp2 = signalsResp2 s\<rparr>,
      \<lparr>ik = ik s', secret = secret s', progress = progress s',
       signalsInit = signalsInit s', signalsResp = signalsResp s',
       signalsInit2 = signalsInit2 s', signalsResp2 = signalsResp2 s'\<rparr>)
           \<in> skl1_step4 Rb A B Ni gnx"
    apply (auto simp add: l2_step4_def, auto simp add: skl1_step4_def)
    apply (auto simp add: can_signal_def)
    done
qed

text \<open>attacker events\<close>
lemma l2_dy_fake_chan_refines_skip:
  "{R12s} Id, l2_dy_fake_chan M {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_defs)


lemma l2_dy_fake_msg_refines_learn:
  "{R12s \<inter> UNIV \<times> (l2_inv3 \<inter> l2_inv7)} l1_learn m, l2_dy_fake_msg m {>R12s}"
apply (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)
apply (drule Fake_insert_dy_fake_msg, erule l2_inv3D [THEN conjunct1])
apply (auto dest!: l2_inv7_aux)
done

text \<open>compromising events\<close>
lemma l2_lkr_others_refines_skip:
  "{R12s} Id, l2_lkr_others A {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)

lemma l2_lkr_after_refines_skip:
  "{R12s} Id, l2_lkr_after A {>R12s}"
by (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)

lemma l2_skr_refines_learn:
  "{R12s \<inter> UNIV \<times> (l2_inv2 \<inter> l2_inv3 \<inter> l2_inv7)} l1_learn K, l2_skr R K {>R12s}"
proof (auto simp add: PO_rhoare_defs R12s_defs l2_loc_defs l1_defs)
  fix s :: l2_state fix x
  assume H:
    "s \<in> l2_inv2" "s \<in> l2_inv3"
    "R \<notin> partners" "R \<noteq> test" "in_progress (progress s R) xsk" "guessed_frame R xsk = Some K"
  assume Hx:"x \<in> synth (analz (insert K (ik s)))"
  assume "x \<in> secret s" "s \<in> l2_inv7"
  then obtain R R' N N' where Hx':"x = Exp (Exp Gen (NonceF (R$N))) (NonceF (R'$N'))"
                                "R = test \<and> R' \<in> partners \<and> (N=nx \<or> N=ny) \<and> (N'=nx \<or> N'=ny)"
    by (auto dest!: l2_inv7D subsetD)
  from H have "s \<lparr>ik := insert K (ik s)\<rparr> \<in> l2_inv3"
    by (auto intro: hoare_apply [OF l2_inv3_skr] simp add: l2_defs)
  with Hx have "x \<in> synth (analz (generators (s \<lparr>ik := insert K (ik s)\<rparr>)))"
    by (auto dest: l2_inv3D_aux)
  with Hx' show False
    by (auto dest!: Exp_Exp_Gen_synth dest: Exp_Exp_Gen_inj2 simp add: analz_generators)
qed


text \<open>Refinement proof.\<close>

lemmas l2_trans_refines_l1_trans = 
  l2_dy_fake_msg_refines_learn l2_dy_fake_chan_refines_skip
  l2_lkr_others_refines_skip l2_lkr_after_refines_skip l2_skr_refines_learn
  l2_step1_refines_step1 l2_step2_refines_step2 l2_step3_refines_step3 l2_step4_refines_step4

lemma l2_refines_init_l1 [iff]:
  "init l2 \<subseteq> R12s `` (init skl1)"
by (auto simp add: R12s_defs skl1_defs l2_loc_defs)

lemma l2_refines_trans_l1 [iff]:
  "{R12s \<inter> (UNIV \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv5 \<inter> 
                     l2_inv6 \<inter> l2_inv6' \<inter> l2_inv7))}
     trans skl1, trans l2
   {> R12s}"
by (auto 0 3 simp add: skl1_def l2_def skl1_trans_def l2_trans_def
             intro!: l2_trans_refines_l1_trans)

lemma PO_obs_consistent_R12s [iff]: 
  "obs_consistent R12s med12s skl1 l2"
by (auto simp add: obs_consistent_def R12s_def med12s_def l2_defs)

lemma l2_refines_l1 [iff]:
  "refines 
     (R12s \<inter> 
      (reach skl1 \<times> (l2_inv1 \<inter> l2_inv2 \<inter> l2_inv3 \<inter> l2_inv4 \<inter> l2_inv5 \<inter>
                                                  l2_inv6 \<inter> l2_inv6' \<inter> l2_inv7)))
     med12s skl1 l2"
by (rule Refinement_using_invariants, auto)

lemma l2_implements_l1 [iff]:
  "implements med12s skl1 l2"
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
         [OF skl1_obs_secrecy _ l2_implements_l1])
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
         [OF skl1_obs_iagreement_Init _ l2_implements_l1])
apply (auto simp add: med12s_def l1_iagreement_Init_def)
done

lemma l2_iagreement_Init [iff]: "reach l2 \<subseteq> l2_iagreement_Init"
by (rule external_to_internal_invariant [OF l2_obs_iagreement_Init], auto)

abbreviation "l2_iagreement_Resp \<equiv> l1_iagreement_Resp"

lemma l2_obs_iagreement_Resp [iff]: "oreach l2 \<subseteq> l2_iagreement_Resp"
apply (rule external_invariant_translation 
         [OF skl1_obs_iagreement_Resp _ l2_implements_l1])
apply (auto simp add: med12s_def l1_iagreement_Resp_def)
done

lemma l2_iagreement_Resp [iff]: "reach l2 \<subseteq> l2_iagreement_Resp"
by (rule external_to_internal_invariant [OF l2_obs_iagreement_Resp], auto)

end
