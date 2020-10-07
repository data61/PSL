(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  pfslvl3.thy (Isabelle/HOL 2016-1)
  ID:      $Id: pfslvl3.thy 133183 2017-01-31 13:55:43Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Generic Level 3 protocol using ephemeral asymmetric keys to achieve 
  forward secrecy.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Key Transport Protocol with PFS (L3 locale)\<close>

theory pfslvl3
imports pfslvl2 Implem_lemmas
begin


(**************************************************************************************************)
subsection \<open>State and Events\<close>
(**************************************************************************************************)

text \<open>Level 3 state\<close>
text \<open>(The types have to be defined outside the locale.)\<close>

record l3_state = l1_state +  
  bad :: "agent set"

type_synonym l3_obs = "l3_state"

type_synonym
  l3_pred = "l3_state set"

type_synonym
  l3_trans = "(l3_state \<times> l3_state) set"


text \<open>attacker event\<close>
definition
  l3_dy :: "msg \<Rightarrow> l3_trans"
where
  "l3_dy \<equiv> ik_dy"



text \<open>compromise events\<close>
definition
  l3_lkr_others :: "agent \<Rightarrow> l3_trans"
where
  "l3_lkr_others A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    A \<noteq> test_owner \<and>
    A \<noteq> test_partner \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s,
           ik := keys_of A \<union> ik s\<rparr>
  }"

definition
  l3_lkr_actor :: "agent \<Rightarrow> l3_trans"
where
  "l3_lkr_actor A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    A = test_owner \<and>
    A \<noteq> test_partner \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s,
           ik := keys_of A \<union> ik s\<rparr>
  }"

definition
  l3_lkr_after :: "agent \<Rightarrow> l3_trans"
where
  "l3_lkr_after A \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    test_ended s \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>bad := {A} \<union> bad s,
           ik := keys_of A \<union> ik s\<rparr>
  }"

definition
  l3_skr :: "rid_t \<Rightarrow> msg \<Rightarrow> l3_trans"
where
  "l3_skr R K \<equiv> {(s,s').
    \<comment> \<open>guards\<close>
    R \<noteq> test \<and> R \<notin> partners \<and>
    in_progress (progress s R) xsk \<and>
    guessed_frame R xsk = Some K \<and>
    \<comment> \<open>actions\<close>
    s' = s\<lparr>ik := {K} \<union> ik s\<rparr>
  }"

text \<open>New locale for the level 3 protocol\<close>
text \<open>This locale does not add new assumptions, it is only used to separate the level 3
protocol from the implementation locale.\<close>
locale pfslvl3 = valid_implem
begin

text \<open>protocol events\<close>
definition
    l3_step1 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> l3_trans"
where
  "l3_step1 Ra A B \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    Ra \<notin> dom (progress s) \<and>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      progress := (progress s)(Ra \<mapsto> {xpkE, xskE}),
      ik := {implAuth A B \<langle>Number 0, epubKF (Ra$kE)\<rangle>} \<union> (ik s)
      \<rparr>
  }"

definition
  l3_step2 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l3_trans"
where
  "l3_step2 Rb A B KE \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Rb = \<lparr>role=Resp, owner=B, partner=A\<rparr> \<and>
    Rb \<notin> dom (progress s) \<and>
    guessed_frame Rb xpkE = Some KE \<and>
    implAuth A B \<langle>Number 0, KE\<rangle> \<in> ik s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr>
      progress := (progress s)(Rb \<mapsto> {xpkE, xsk}),
      ik := {implAuth B A (Aenc (NonceF (Rb$sk)) KE)} \<union> (ik s),
      signals := if can_signal s A B then
                   addSignal (signals s) (Running A B \<langle>KE, NonceF (Rb$sk)\<rangle>)
                 else
                   signals s,
      secret := {x. x = NonceF (Rb$sk) \<and> Rb = test} \<union> secret s
         \<rparr>
  }"  


definition
  l3_step3 :: "rid_t \<Rightarrow> agent \<Rightarrow> agent \<Rightarrow> msg \<Rightarrow> l3_trans"
where
  "l3_step3 Ra A B K \<equiv> {(s, s').
    \<comment> \<open>guards:\<close>
    guessed_runs Ra = \<lparr>role=Init, owner=A, partner=B\<rparr> \<and>
    progress s Ra = Some {xpkE, xskE} \<and>
    guessed_frame Ra xsk = Some K \<and>
    implAuth B A (Aenc K (epubKF (Ra$kE))) \<in> ik s \<and>
    \<comment> \<open>actions:\<close>
    s' = s\<lparr> progress := (progress s)(Ra \<mapsto> {xpkE, xskE, xsk}),
            signals := if can_signal s A B then
                         addSignal (signals s) (Commit A B \<langle>epubKF (Ra$kE), K\<rangle>)
                       else
                         signals s,
            secret := {x. x = K \<and> Ra = test} \<union> secret s
          \<rparr>
  }"



text \<open>specification\<close>

text \<open>initial compromise\<close>

definition
  ik_init :: "msg set"
where
  "ik_init \<equiv> {priK C |C. C \<in> bad_init} \<union> {pubK A | A. True} \<union> 
             {shrK A B |A B. A \<in> bad_init \<or> B \<in> bad_init} \<union> Tags"

text \<open>lemmas about @{term "ik_init"}\<close>
lemma parts_ik_init [simp]: "parts ik_init = ik_init"
by (auto elim!: parts.induct, auto simp add: ik_init_def)

lemma analz_ik_init [simp]: "analz ik_init = ik_init"
by (auto dest: analz_into_parts)

lemma abs_ik_init [iff]: "abs ik_init = {}"
apply (auto elim!: absE)
apply (auto simp add: ik_init_def)
done

lemma payloadSet_ik_init [iff]: "ik_init \<inter> payload = {}"
by (auto simp add: ik_init_def)

lemma validSet_ik_init [iff]: "ik_init \<inter> valid = {}"
by (auto simp add: ik_init_def)


definition 
  l3_init :: "l3_state set"
where
  "l3_init \<equiv> { \<lparr>
    ik = ik_init,
    secret = {},
    progress = Map.empty,
    signals = \<lambda>x. 0,
    bad = bad_init
    \<rparr>}"

lemmas l3_init_defs = l3_init_def ik_init_def

definition 
l3_trans :: "l3_trans"
where
  "l3_trans \<equiv> (\<Union>m M KE Rb Ra A B K.
     l3_step1 Ra A B \<union>
     l3_step2 Rb A B KE \<union>
     l3_step3 Ra A B m \<union>
     l3_dy M \<union>
     l3_lkr_others A \<union>
     l3_lkr_after A \<union>
     l3_skr Ra K \<union>
     Id
  )"


definition 
  l3 :: "(l3_state, l3_obs) spec" where
  "l3 \<equiv> \<lparr>
    init = l3_init,
    trans = l3_trans,
    obs = id
  \<rparr>"

lemmas l3_loc_defs = 
  l3_step1_def l3_step2_def l3_step3_def
  l3_def l3_init_defs l3_trans_def
  l3_dy_def
  l3_lkr_others_def l3_lkr_after_def l3_skr_def

lemmas l3_defs = l3_loc_defs ik_dy_def
lemmas l3_nostep_defs = l3_def l3_init_def l3_trans_def


lemma l3_obs_id [simp]: "obs l3 = id"
by (simp add: l3_def)


(**************************************************************************************************)
subsection \<open>Invariants\<close>
(**************************************************************************************************)
subsubsection \<open>inv1: No long-term keys as message parts\<close>
(**************************************************************************************************)

definition
  l3_inv1 :: "l3_state set"
where
  "l3_inv1 \<equiv> {s.
     parts (ik s) \<inter> range LtK \<subseteq> ik s
  }"

lemmas l3_inv1I = l3_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv1E [elim] = l3_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv1D = l3_inv1_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv1D' [dest]: "\<lbrakk> LtK K \<in> parts (ik s); s \<in> l3_inv1\<rbrakk> \<Longrightarrow> LtK K \<in> ik s"
by (auto simp add: l3_inv1_def)

lemma l3_inv1_init [iff]:
  "init l3 \<subseteq> l3_inv1"
by (auto simp add: l3_def l3_init_def intro!:l3_inv1I)

lemma l3_inv1_trans [iff]:
  "{l3_inv1} trans l3 {> l3_inv1}"
apply (auto simp add: PO_hoare_defs l3_nostep_defs intro!: l3_inv1I)
apply (auto simp add: l3_defs dy_fake_msg_def dy_fake_chan_def
        parts_insert [where H="ik _"] parts_insert [where H="insert _ (ik _)"]
        dest!: Fake_parts_insert)
apply (auto dest:analz_into_parts)
done

lemma PO_l3_inv1 [iff]:
  "reach l3 \<subseteq> l3_inv1"
by (rule inv_rule_basic) (auto)



subsubsection \<open>inv2: @{term "bad s"} indeed contains "bad" keys\<close>
(**************************************************************************************************)

definition
  l3_inv2 :: "l3_state set"
where
  "l3_inv2 \<equiv> {s.
    Keys_bad (ik s) (bad s)
  }"

lemmas l3_inv2I = l3_inv2_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv2E [elim] = l3_inv2_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv2D = l3_inv2_def [THEN setc_def_to_dest, rule_format]


lemma l3_inv2_init [simp,intro!]:
  "init l3 \<subseteq> l3_inv2"
by (auto simp add: l3_def l3_init_defs intro!:l3_inv2I Keys_badI)

lemma l3_inv2_trans [simp,intro!]:
  "{l3_inv2 \<inter> l3_inv1} trans l3 {> l3_inv2}"
apply (auto simp add: PO_hoare_defs l3_nostep_defs intro!: l3_inv2I)
apply (auto simp add: l3_defs dy_fake_msg_def dy_fake_chan_def)
text \<open>4 subgoals: dy, lkr*, skr\<close>
apply (auto intro: Keys_bad_insert_Fake Keys_bad_insert_keys_of)
apply (auto intro!: Keys_bad_insert_payload)
done

lemma PO_l3_inv2 [iff]: "reach l3 \<subseteq> l3_inv2"
by (rule_tac J="l3_inv1" in inv_rule_incr) (auto)



subsubsection \<open>inv3\<close>
(**************************************************************************************************)

text \<open>If a message can be analyzed from the intruder knowledge then it can
be derived (using synth/analz) from the sets of implementation, non-implementation, and
long-term key messages and the tags. That is, intermediate messages are not needed.
\<close>


definition
  l3_inv3 :: "l3_state set"      
where
  "l3_inv3 \<equiv> {s.
    analz (ik s) \<subseteq> 
    synth (analz ((ik s \<inter> payload) \<union> ((ik s) \<inter> valid) \<union> (ik s \<inter> range LtK) \<union> Tags))
  }"

lemmas l3_inv3I = l3_inv3_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv3E = l3_inv3_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv3D = l3_inv3_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv3_init [iff]:
  "init l3 \<subseteq> l3_inv3"
apply (auto simp add: l3_def l3_init_def intro!: l3_inv3I)
apply (auto simp add: ik_init_def intro!: synth_increasing [THEN [2] rev_subsetD])
done

declare domIff [iff del]

text \<open>Most of the cases in this proof are simple and very similar.
The proof could probably be shortened.\<close>
lemma l3_inv3_trans [simp,intro!]:
  "{l3_inv3} trans l3 {> l3_inv3}"
proof (simp add: l3_nostep_defs, safe)
  fix Ra A B
  show "{l3_inv3} l3_step1 Ra A B {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    apply (auto intro!: validI dest!: analz_insert_partition [THEN [2] rev_subsetD])
    done
next
  fix Rb A B KE
  show "{l3_inv3} l3_step2 Rb A B KE {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    apply (auto intro!: validI dest!: analz_insert_partition [THEN [2] rev_subsetD])
    done
next
  fix Ra A B K
  show "{l3_inv3} l3_step3 Ra A B K {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    done
next
  fix m 
  show "{l3_inv3} l3_dy m {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs dy_fake_chan_def dy_fake_msg_def
                intro!: l3_inv3I dest!: l3_inv3D)
    apply (drule synth_analz_insert)
    apply (blast intro: synth_analz_monotone dest: synth_monotone)
    done
next
  fix A
  show "{l3_inv3} l3_lkr_others A {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    apply (drule analz_Un_partition [of _ "keys_of A"], auto)
    done
next
  fix A
  show "{l3_inv3} l3_lkr_after A {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    apply (drule analz_Un_partition [of _ "keys_of A"], auto)
    done
next
  fix R K
  show "{l3_inv3} l3_skr R K {> l3_inv3}"
    apply (auto simp add: PO_hoare_def l3_defs intro!: l3_inv3I dest!: l3_inv3D)
    apply (auto dest!: analz_insert_partition [THEN [2] rev_subsetD])
    done
qed

lemma PO_l3_inv3 [iff]: "reach l3 \<subseteq> l3_inv3"
by (rule inv_rule_basic) (auto)



subsubsection \<open>inv4: the intruder knows the tags\<close>
(**************************************************************************************************)

definition
  l3_inv4 :: "l3_state set"
where
  "l3_inv4 \<equiv> {s.
    Tags \<subseteq> ik s
  }"

lemmas l3_inv4I = l3_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv4E [elim] = l3_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv4D = l3_inv4_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv4_init [simp,intro!]:
  "init l3 \<subseteq> l3_inv4"
by (auto simp add: l3_def l3_init_def ik_init_def intro!:l3_inv4I)

lemma l3_inv4_trans [simp,intro!]:
  "{l3_inv4} trans l3 {> l3_inv4}"
apply (auto simp add: PO_hoare_defs l3_nostep_defs intro!: l3_inv4I)
apply (auto simp add: l3_defs dy_fake_chan_def dy_fake_msg_def)
done

lemma PO_l3_inv4 [simp,intro!]: "reach l3 \<subseteq> l3_inv4"
by (rule inv_rule_basic) (auto)


text \<open>The remaining invariants are derived from the others.
They are not protocol dependent provided the previous invariants hold.\<close>

subsubsection \<open>inv5\<close>
(**************************************************************************************************)

text \<open>The messages that the L3 DY intruder can derive from the intruder knowledge 
(using @{term "synth"}/@{term "analz"}), are either implementations or intermediate messages or
can also be derived by the L2 intruder from the set 
@{term "extr (bad s) ((ik s) \<inter> payload) (abs (ik s))"}, that is, given the 
non-implementation messages and the abstractions of (implementation) messages
in the intruder knowledge. 
\<close>

definition
  l3_inv5 :: "l3_state set"
where
  "l3_inv5 \<equiv> {s.
    synth (analz (ik s)) \<subseteq> 
    dy_fake_msg (bad s) (ik s \<inter> payload) (abs (ik s)) \<union> -payload
  }"

lemmas l3_inv5I = l3_inv5_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv5E = l3_inv5_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv5D = l3_inv5_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv5_derived: "l3_inv2 \<inter> l3_inv3 \<subseteq> l3_inv5"
by (auto simp add: abs_validSet dy_fake_msg_def intro!: l3_inv5I
            dest!: l3_inv3D [THEN synth_mono, THEN [2] rev_subsetD]
            dest!: synth_analz_NI_I_K_synth_analz_NI_E [THEN [2] rev_subsetD])

lemma PO_l3_inv5 [simp,intro!]: "reach l3 \<subseteq> l3_inv5"
using l3_inv5_derived PO_l3_inv2 PO_l3_inv3 
by blast

subsubsection \<open>inv6\<close>
(**************************************************************************************************)

text \<open>If the level 3 intruder can deduce a message implementing an insecure channel message, then:
\begin{itemize}
  \item either the message is already in the intruder knowledge;
  \item or the message is constructed, and the payload can also be deduced by the intruder.
\end{itemize}
\<close>

definition
  l3_inv6 :: "l3_state set"
where
  "l3_inv6 \<equiv> {s. \<forall> A B M. 
     (implInsec A B M \<in> synth (analz (ik s)) \<and> M \<in> payload) \<longrightarrow> 
     (implInsec A B M \<in> ik s \<or> M \<in> synth (analz (ik s)))
  }"

lemmas l3_inv6I = l3_inv6_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv6E = l3_inv6_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv6D = l3_inv6_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv6_derived [simp,intro!]:
  "l3_inv3 \<inter> l3_inv4 \<subseteq> l3_inv6"
apply (auto intro!: l3_inv6I dest!: l3_inv3D)
text \<open>1 subgoal\<close>
apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implInsec_synth_analz [rotated 1, where H="_ \<union> _"])
apply (auto dest!: synth_analz_monotone [of _ "_ \<union> _" "ik _"])
done

lemma PO_l3_inv6 [simp,intro!]: "reach l3 \<subseteq> l3_inv6"
using l3_inv6_derived PO_l3_inv3 PO_l3_inv4
by (blast)

subsubsection \<open>inv7\<close>
(**************************************************************************************************)

text \<open>If the level 3 intruder can deduce a message implementing a confidential channel message,
then:
\begin{itemize}
 \item either the message is already in the intruder knowledge;
 \item or the message is constructed, and the payload can also be deduced by the intruder.
\end{itemize}
\<close>

definition
  l3_inv7 :: "l3_state set"
where
  "l3_inv7 \<equiv> {s. \<forall> A B M. 
     (implConfid A B M \<in> synth (analz (ik s)) \<and> M \<in> payload) \<longrightarrow> 
     (implConfid A B M \<in> ik s \<or> M \<in> synth (analz (ik s)))
  }"

lemmas l3_inv7I = l3_inv7_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv7E = l3_inv7_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv7D = l3_inv7_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv7_derived [simp,intro!]:
  "l3_inv3 \<inter> l3_inv4 \<subseteq> l3_inv7"
apply (auto intro!: l3_inv7I dest!: l3_inv3D)
text \<open>1 subgoal\<close>
apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implConfid_synth_analz [rotated 1, where H="_ \<union> _"])
apply (auto dest!: synth_analz_monotone [of _ "_ \<union> _" "ik _"])
done

lemma PO_l3_inv7 [simp,intro!]: "reach l3 \<subseteq> l3_inv7"
using l3_inv7_derived PO_l3_inv3 PO_l3_inv4
by (blast)


subsubsection \<open>inv8\<close>
(**************************************************************************************************)

text \<open>If the level 3 intruder can deduce a message implementing an authentic channel message then:
\begin{itemize}
  \item either the message is already in the intruder knowledge;
  \item or the message is constructed, and in this case the payload can also be deduced
     by the intruder, and one of the agents is bad.
\end{itemize}
\<close>


definition
  l3_inv8 :: "l3_state set"
where
  "l3_inv8 \<equiv> {s. \<forall> A B M. 
     (implAuth A B M \<in> synth (analz (ik s)) \<and> M \<in> payload) \<longrightarrow> 
     (implAuth A B M \<in> ik s \<or> (M \<in> synth (analz (ik s)) \<and> (A \<in> bad s \<or> B \<in> bad s)))
  }"

lemmas l3_inv8I = l3_inv8_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv8E = l3_inv8_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv8D = l3_inv8_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv8_derived [iff]:
  "l3_inv2 \<inter> l3_inv3 \<inter> l3_inv4 \<subseteq> l3_inv8"
apply (auto intro!: l3_inv8I dest!: l3_inv3D l3_inv2D)
text \<open>2 subgoals: M is deducible and the agents are bad\<close>
apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implAuth_synth_analz [rotated 1, where H="_ \<union> _"] elim!: synth_analz_monotone)

apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implAuth_synth_analz [rotated 1, where H="_ \<union> _"])
done

lemma PO_l3_inv8 [iff]: "reach l3 \<subseteq> l3_inv8"
using l3_inv8_derived
  PO_l3_inv3 PO_l3_inv2 PO_l3_inv4
by blast


subsubsection \<open>inv9\<close>
(**************************************************************************************************)

text \<open>If the level 3 intruder can deduce a message implementing a secure channel message then:
\begin{itemize}
  \item either the message is already in the intruder knowledge;
  \item or the message is constructed, and in this case the payload can also be deduced 
 by the intruder, and one of the agents is bad.
\end{itemize}
\<close>

definition
  l3_inv9 :: "l3_state set"
where
  "l3_inv9 \<equiv> {s. \<forall> A B M. 
     (implSecure A B M \<in> synth (analz (ik s)) \<and> M \<in> payload) \<longrightarrow> 
     (implSecure A B M \<in> ik s \<or> (M \<in> synth (analz (ik s)) \<and> (A \<in> bad s \<or> B \<in> bad s)))
  }"

lemmas l3_inv9I = l3_inv9_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv9E = l3_inv9_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv9D = l3_inv9_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv9_derived [iff]:
  "l3_inv2 \<inter> l3_inv3 \<inter> l3_inv4 \<subseteq> l3_inv9"
apply (auto intro!: l3_inv9I dest!:l3_inv3D l3_inv2D)
text \<open>2 subgoals: M is deducible and the agents are bad\<close>
apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implSecure_synth_analz [rotated 1, where H="_ \<union> _"] elim!: synth_analz_monotone)

apply (drule synth_mono, simp, drule subsetD, assumption)
apply (auto dest!: implSecure_synth_analz [rotated 1, where H="_ \<union> _"])
done

lemma PO_l3_inv9 [iff]: "reach l3 \<subseteq> l3_inv9"
using l3_inv9_derived
  PO_l3_inv3 PO_l3_inv2 PO_l3_inv4
by blast


(**************************************************************************************************)
subsection \<open>Refinement\<close>
(**************************************************************************************************)

text \<open>mediator function\<close>
definition 
  med23s :: "l3_obs \<Rightarrow> l2_obs"
where
  "med23s t \<equiv> \<lparr>
    ik = ik t \<inter> payload,
    secret = secret t,
    progress = progress t,
    signals = signals t,
    chan = abs (ik t),
    bad = bad t
    \<rparr>"

text \<open>relation between states\<close>
definition
  R23s :: "(l2_state * l3_state) set"
where
  "R23s \<equiv> {(s, s').
    s = med23s s'
    }"

lemmas R23s_defs = R23s_def med23s_def


lemma R23sI: 
  "\<lbrakk> ik s = ik t \<inter> payload; secret s = secret t; progress s = progress t; signals s = signals t;
     chan s = abs (ik t); l2_state.bad s = bad t \<rbrakk> 
 \<Longrightarrow> (s, t) \<in> R23s"
by (auto simp add: R23s_def med23s_def)

lemma R23sD: 
  "(s, t) \<in> R23s \<Longrightarrow>
    ik s = ik t \<inter> payload \<and> secret s = secret t \<and> progress s = progress t \<and> signals s = signals t \<and>
    chan s = abs (ik t) \<and> l2_state.bad s = bad t"
by (auto simp add: R23s_def med23s_def)

lemma R23sE [elim]: 
  "\<lbrakk> (s, t) \<in> R23s;
     \<lbrakk> ik s = ik t \<inter> payload; secret s = secret t; progress s = progress t; signals s = signals t;
     chan s = abs (ik t); l2_state.bad s = bad t \<rbrakk> \<Longrightarrow> P \<rbrakk> 
 \<Longrightarrow> P"
by (auto simp add: R23s_def med23s_def)

lemma can_signal_R23 [simp]:
  "(s2, s3) \<in> R23s \<Longrightarrow>
   can_signal s2 A B \<longleftrightarrow> can_signal s3 A B"
by (auto simp add: can_signal_def)


subsubsection \<open>Protocol events\<close>
(**************************************************************************************************)

lemma l3_step1_refines_step1:
  "{R23s} l2_step1 Ra A B, l3_step1 Ra A B {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)
apply (auto simp add: l3_defs l2_step1_def)
done

lemma l3_step2_refines_step2:
  "{R23s} l2_step2 Rb A B KE, l3_step2 Rb A B KE{>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs l2_step2_def)
apply (auto simp add: l3_step2_def)
done

lemma l3_step3_refines_step3:
  "{R23s} l2_step3 Ra A B K, l3_step3 Ra A B K {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs l2_step3_def)
apply (auto simp add: l3_step3_def)
done


subsubsection \<open>Intruder events\<close>
(**************************************************************************************************)

lemma l3_dy_payload_refines_dy_fake_msg:
  "M \<in> payload \<Longrightarrow>
   {R23s \<inter> UNIV \<times> l3_inv5} l2_dy_fake_msg M, l3_dy M {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)
apply (auto simp add: l3_defs l2_dy_fake_msg_def dest: l3_inv5D)
done

lemma l3_dy_valid_refines_dy_fake_chan:
  "\<lbrakk> M \<in> valid; M' \<in> abs {M} \<rbrakk> \<Longrightarrow>
   {R23s \<inter> UNIV \<times> (l3_inv5 \<inter> l3_inv6 \<inter> l3_inv7 \<inter> l3_inv8 \<inter> l3_inv9)} 
      l2_dy_fake_chan M', l3_dy M 
   {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs, simp add: l2_dy_fake_chan_def)
apply (auto simp add: l3_defs)
text \<open>1 subgoal\<close>
apply (erule valid_cases, simp_all add: dy_fake_chan_def)
  text \<open>Insec\<close>
  apply (blast dest: l3_inv6D l3_inv5D)
  text \<open>Confid\<close>
  apply (blast dest: l3_inv7D l3_inv5D)
  text \<open>Auth\<close>
  apply (blast dest: l3_inv8D l3_inv5D)
  text \<open>Secure\<close>
  apply (blast dest: l3_inv9D l3_inv5D)
done


lemma l3_dy_valid_refines_dy_fake_chan_Un:
  "M \<in> valid \<Longrightarrow>
   {R23s \<inter> UNIV \<times> (l3_inv5 \<inter> l3_inv6 \<inter> l3_inv7 \<inter> l3_inv8 \<inter> l3_inv9)} 
      \<Union>M'. l2_dy_fake_chan M', l3_dy M 
   {>R23s}"
by (auto dest: valid_abs intro: l3_dy_valid_refines_dy_fake_chan)


lemma l3_dy_isLtKey_refines_skip:
  "{R23s} Id, l3_dy (LtK ltk) {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs l3_defs)
apply (auto elim!: absE)
done

lemma l3_dy_others_refines_skip:
  "\<lbrakk> M \<notin> range LtK; M \<notin> valid; M \<notin> payload \<rbrakk> \<Longrightarrow> 
   {R23s} Id, l3_dy M {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)     (* auto SLOW *)
apply (auto simp add: l3_defs)
apply (auto elim!: absE intro: validI)
done


lemma l3_dy_refines_dy_fake_msg_dy_fake_chan_skip:
   "{R23s \<inter> UNIV \<times> (l3_inv5 \<inter> l3_inv6 \<inter> l3_inv7 \<inter> l3_inv8 \<inter> l3_inv9)} 
      l2_dy_fake_msg M \<union> (\<Union>M'. l2_dy_fake_chan M') \<union> Id, l3_dy M 
    {>R23s}"
by (cases "M \<in> payload \<union> valid \<union> range LtK")
   (auto dest: l3_dy_payload_refines_dy_fake_msg l3_dy_valid_refines_dy_fake_chan_Un 
         intro: l3_dy_isLtKey_refines_skip dest!: l3_dy_others_refines_skip)


subsubsection \<open>Compromise events\<close>
(**************************************************************************************************)

lemma l3_lkr_others_refines_lkr_others:
  "{R23s} l2_lkr_others A, l3_lkr_others A {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)
apply (auto simp add: l3_defs l2_lkr_others_def)
done

lemma l3_lkr_after_refines_lkr_after:
  "{R23s} l2_lkr_after A, l3_lkr_after A {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)
apply (auto simp add: l3_defs l2_lkr_after_def)
done

lemma l3_skr_refines_skr:
  "{R23s} l2_skr R K, l3_skr R K {>R23s}"
apply (auto simp add: PO_rhoare_defs R23s_defs)
apply (auto simp add: l3_defs l2_skr_def)
done



lemmas l3_trans_refines_l2_trans = 
  l3_step1_refines_step1 l3_step2_refines_step2 l3_step3_refines_step3
  l3_dy_refines_dy_fake_msg_dy_fake_chan_skip
  l3_lkr_others_refines_lkr_others l3_lkr_after_refines_lkr_after l3_skr_refines_skr



lemma l3_refines_init_l2 [iff]:
  "init l3 \<subseteq> R23s `` (init l2)"
by (auto simp add: R23s_defs l2_defs l3_def l3_init_def)

lemma l3_refines_trans_l2 [iff]:
  "{R23s \<inter> (UNIV \<times> (l3_inv1 \<inter> l3_inv2 \<inter> l3_inv3 \<inter> l3_inv4))} trans l2, trans l3 {> R23s}"
proof -
  let ?pre' = "R23s \<inter> (UNIV \<times> (l3_inv5 \<inter> l3_inv6 \<inter> l3_inv7 \<inter> l3_inv8 \<inter> l3_inv9))"
  show ?thesis (is "{?pre} ?t1, ?t2 {>?post}")
  proof (rule relhoare_conseq_left)
    show "?pre \<subseteq> ?pre'"
      using l3_inv5_derived l3_inv6_derived l3_inv7_derived l3_inv8_derived l3_inv9_derived by blast
  next 
    show "{?pre'} ?t1, ?t2 {> ?post}" 
      by (auto simp add: l2_def l3_def l2_trans_def l3_trans_def
               intro!: l3_trans_refines_l2_trans)
  qed
qed    

lemma PO_obs_consistent_R23s [iff]: 
  "obs_consistent R23s med23s l2 l3"
by (auto simp add: obs_consistent_def R23s_def med23s_def l2_defs)


lemma l3_refines_l2 [iff]:
  "refines 
     (R23s \<inter> 
      (reach l2 \<times> (l3_inv1 \<inter> l3_inv2 \<inter> l3_inv3 \<inter> l3_inv4)))
     med23s l2 l3"
by (rule Refinement_using_invariants, auto)

lemma l3_implements_l2 [iff]:
  "implements med23s l2 l3"
by (rule refinement_soundness) (auto)


(**************************************************************************************************)
subsection \<open>Derived invariants\<close>
(**************************************************************************************************)

subsubsection \<open>inv10: secrets contain no implementation material\<close>
(**************************************************************************************************)

definition
  l3_inv10 :: "l3_state set"
where
  "l3_inv10 \<equiv> {s.
    secret s \<subseteq> payload
  }"

lemmas l3_inv10I = l3_inv10_def [THEN setc_def_to_intro, rule_format]
lemmas l3_inv10E = l3_inv10_def [THEN setc_def_to_elim, rule_format]
lemmas l3_inv10D = l3_inv10_def [THEN setc_def_to_dest, rule_format]

lemma l3_inv10_init [iff]: 
  "init l3 \<subseteq> l3_inv10"
by (auto simp add: l3_def l3_init_def ik_init_def intro!:l3_inv10I)

lemma l3_inv10_trans [iff]:
  "{l3_inv10} trans l3 {> l3_inv10}"
apply (auto simp add: PO_hoare_defs l3_nostep_defs)
apply (auto simp add: l3_defs l3_inv10_def)
done

lemma PO_l3_inv10 [iff]: "reach l3 \<subseteq> l3_inv10"
by (rule inv_rule_basic) (auto)

lemma l3_obs_inv10 [iff]: "oreach l3 \<subseteq> l3_inv10"
by (auto simp add: oreach_def)



subsubsection \<open>Partial secrecy\<close>
(**************************************************************************************************)

text \<open>We want to prove @{term "l3_secrecy"}, ie
  @{term "synth (analz (ik s)) \<inter> secret s = {}"},
  but by refinement we only get @{term "l3_partial_secrecy"}: 
    @{term "dy_fake_msg (bad s) (payloadSet (ik s)) (abs (ik s)) \<inter> secret s = {}"}.
  This is fine if secrets contain no implementation material.
  Then, by @{term "inv5"}, a message in @{term "synth (analz (ik s))"} is in
    @{term "dy_fake_msg (bad s) (payloadSet (ik s)) (abs (ik s)) \<union> -payload"},
  and @{term "l3_partial_secrecy"} proves it is not a secret.
\<close>

definition
  l3_partial_secrecy :: "('a l3_state_scheme) set"
where
  "l3_partial_secrecy \<equiv> {s. 
    dy_fake_msg (bad s) (ik s \<inter> payload) (abs (ik s)) \<inter> secret s = {}
  }"


lemma l3_obs_partial_secrecy [iff]: "oreach l3 \<subseteq> l3_partial_secrecy"
apply (rule external_invariant_translation [OF l2_obs_secrecy _ l3_implements_l2])
apply (auto simp add: med23s_def l2_secrecy_def l3_partial_secrecy_def)
done


subsubsection \<open>Secrecy\<close>
(**************************************************************************************************)

definition 
  l3_secrecy :: "('a l3_state_scheme) set"
where
  "l3_secrecy \<equiv> l1_secrecy"

lemma l3_obs_inv5: "oreach l3 \<subseteq> l3_inv5"
by (auto simp add: oreach_def)

lemma l3_obs_secrecy [iff]: "oreach l3 \<subseteq> l3_secrecy"
apply (rule, frule l3_obs_inv5 [THEN [2] rev_subsetD], frule l3_obs_inv10 [THEN [2] rev_subsetD])
apply (auto simp add: med23s_def l2_secrecy_def l3_secrecy_def s0_secrecy_def l3_inv10_def)
using l3_partial_secrecy_def apply (blast dest!: l3_inv5D subsetD [OF l3_obs_partial_secrecy])
done

lemma l3_secrecy [iff]: "reach l3 \<subseteq> l3_secrecy"
by (rule external_to_internal_invariant [OF l3_obs_secrecy], auto)


subsubsection \<open>Injective agreement\<close>
(**************************************************************************************************)

abbreviation "l3_iagreement \<equiv> l1_iagreement"

lemma l3_obs_iagreement [iff]: "oreach l3 \<subseteq> l3_iagreement"
apply (rule external_invariant_translation [OF l2_obs_iagreement _ l3_implements_l2])
apply (auto simp add: med23s_def l1_iagreement_def)
done

lemma l3_iagreement [iff]: "reach l3 \<subseteq> l3_iagreement"
by (rule external_to_internal_invariant [OF l3_obs_iagreement], auto)


end
end
