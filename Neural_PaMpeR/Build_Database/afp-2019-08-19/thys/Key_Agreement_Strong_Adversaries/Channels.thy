(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Channels.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Channels.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Channel messages and related message derivations (extract and fake).

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Channel Messages\<close>

theory Channels
imports Message_derivation
begin

(**************************************************************************************************)
subsection \<open>Channel messages\<close>
(**************************************************************************************************)

datatype chan = 
  Chan "tag" "agent" "agent" "msg"


abbreviation 
  Insec :: "[agent, agent, msg] \<Rightarrow> chan" where
  "Insec \<equiv> Chan insec"

abbreviation 
  Confid :: "[agent, agent, msg] \<Rightarrow> chan" where
  "Confid \<equiv> Chan confid"

abbreviation 
  Auth :: "[agent, agent, msg] \<Rightarrow> chan" where
  "Auth \<equiv> Chan auth"

abbreviation 
  Secure :: "[agent, agent, msg] \<Rightarrow> chan" where
  "Secure \<equiv> Chan secure"


(**************************************************************************************************)
subsection \<open>Extract\<close>
(**************************************************************************************************)

text \<open>The set of payload messages that can be extracted from a set of (crypto) messages 
and a set of channel messages, given a set of bad agents. The second rule states that 
the payload can be extracted from insecure and authentic channels as well as from channels
with a compromised endpoint.\<close>

inductive_set 
  extr :: "agent set \<Rightarrow> msg set \<Rightarrow> chan set \<Rightarrow> msg set"  
  for bad :: "agent set"
  and IK :: "msg set"
  and H :: "chan set"
where 
  extr_Inj: "M \<in> IK \<Longrightarrow> M \<in> extr bad IK H"
| extr_Chan: 
    "\<lbrakk> Chan c A B M \<in> H; c = insec \<or> c = auth \<or> A \<in> bad \<or> B \<in> bad \<rbrakk> \<Longrightarrow> M \<in> extr bad IK H"

declare extr.intros [intro]
declare extr.cases [elim]


lemma extr_empty_chan [simp]: "extr bad IK {} = IK"
by (auto)

lemma IK_subset_extr: "IK \<subseteq> extr bad IK chan"
by (auto)

lemma extr_mono_chan [dest]: "G \<subseteq> H \<Longrightarrow> extr bad IK G \<subseteq> extr bad IK H"
by (safe, erule extr.induct, auto)

lemma extr_mono_IK [dest]: "IK1 \<subseteq> IK2 \<Longrightarrow> extr bad IK1 H \<subseteq> extr bad IK2 H"
by (safe) (erule extr.induct, auto)

lemma extr_mono_bad [dest]: "bad \<subseteq> bad' \<Longrightarrow> extr bad IK H \<subseteq> extr bad' IK H"
by (safe, erule extr.induct, auto)

lemmas extr_monotone_chan [elim] = extr_mono_chan [THEN [2] rev_subsetD]
lemmas extr_monotone_IK [elim] = extr_mono_IK [THEN [2] rev_subsetD]
lemmas extr_monotone_bad [elim] = extr_mono_bad [THEN [2] rev_subsetD]

lemma extr_mono [intro]: "\<lbrakk> b \<subseteq> b'; I \<subseteq> I'; C \<subseteq> C' \<rbrakk> \<Longrightarrow> extr b I C \<subseteq> extr b' I' C'"
by (force)

lemmas extr_monotone [elim] = extr_mono [THEN [2] rev_subsetD]

lemma extr_insert [intro]: "M \<in> extr bad IK H \<Longrightarrow> M \<in> extr bad IK (insert C H)"
by (auto)

lemma extr_insert_Chan [simp]: 
  "extr bad IK (insert (Chan c A B M) H) 
   = (if c = insec \<or> c = auth \<or> A \<in> bad \<or> B \<in> bad 
      then insert M (extr bad IK H) else extr bad IK H)"
by auto

(* do not declare [simp]! *)
lemma extr_insert_chan_eq: "extr bad IK (insert X CH) = extr bad IK {X} \<union> extr bad IK CH"
by (auto)

lemma extr_insert_IK_eq [simp]: "extr bad (insert X IK) CH = insert X (extr bad IK CH)"
by (auto)

lemma extr_insert_bad:
  "extr (insert A bad) IK CH \<subseteq>
   extr bad IK CH \<union> {M. \<exists> B. Confid A B M \<in> CH \<or> Confid B A M \<in> CH \<or>
                             Secure A B M \<in> CH \<or> Secure B A M \<in> CH}"
by (rule, erule extr.induct, auto intro: tag.exhaust)

lemma extr_insert_Confid [simp]:
  "A \<notin> bad \<Longrightarrow>
   B \<notin> bad \<Longrightarrow> 
   extr bad IK (insert (Confid A B X) CH) = extr bad IK CH"
by auto


(**************************************************************************************************)
subsection \<open>Fake\<close>
(**************************************************************************************************)

text \<open>The set of channel messages that an attacker can fake given a set of compromised
agents, a set of crypto messages and a set of channel messages. The second rule states
that an attacker can fake an insecure or confidential messages or a channel message
with a compromised endpoint using a payload that he knows.\<close>

inductive_set 
  fake :: "agent set \<Rightarrow> msg set \<Rightarrow> chan set \<Rightarrow> chan set"
  for bad :: "agent set"
  and IK :: "msg set"
  and chan :: "chan set"
where 
  fake_Inj: "M \<in> chan \<Longrightarrow> M \<in> fake bad IK chan"
| fake_New: 
    "\<lbrakk> M \<in> IK; c = insec \<or> c = confid \<or> A \<in> bad \<or> B \<in> bad  \<rbrakk> 
   \<Longrightarrow> Chan c A B M \<in> fake bad IK chan"

declare fake.cases [elim]
declare fake.intros [intro]

lemmas fake_intros = fake_Inj fake_New

lemma fake_mono_bad [intro]: 
  "bad \<subseteq> bad' \<Longrightarrow> fake bad IK chan \<subseteq> fake bad' IK chan" 
by (auto)

lemma fake_mono_ik [intro]: 
  "IK \<subseteq> IK' \<Longrightarrow> fake bad IK chan \<subseteq> fake bad IK' chan" 
by (auto)

lemma fake_mono_chan [intro]: 
  "chan \<subseteq> chan' \<Longrightarrow> fake bad IK chan \<subseteq> fake bad IK chan'" 
by (auto)

lemma fake_mono [intro]: 
  "\<lbrakk> bad \<subseteq> bad'; IK \<subseteq> IK'; chan \<subseteq> chan'\<rbrakk> \<Longrightarrow> fake bad IK chan \<subseteq> fake bad' IK' chan'" 
by (auto, erule fake.cases, auto)

lemmas fake_monotone_bad [elim] = fake_mono_bad [THEN [2] rev_subsetD]
lemmas fake_monotone_ik [elim] = fake_mono_ik [THEN [2] rev_subsetD]
lemmas fake_monotone_chan [elim] = fake_mono_chan [THEN [2] rev_subsetD]
lemmas fake_monotone [elim] = fake_mono [THEN [2] rev_subsetD]


lemma chan_subset_fake: "chan \<subseteq> fake bad IK chan"
by auto

lemma extr_fake:
  "X \<in> fake bad IK chan \<Longrightarrow> extr bad IK' {X} \<subseteq> IK \<union> extr bad IK' chan"
by auto

lemmas extr_fake_2 [elim] = extr_fake [THEN [2] rev_subsetD]

lemma fake_parts_extr_singleton:  
  "X \<in> fake bad IK chan \<Longrightarrow> parts (extr bad IK' {X}) \<subseteq> parts IK \<union> parts (extr bad IK' chan)"
by (rule extr_fake [THEN parts_mono, simplified])

lemmas fake_parts_extr_singleton_2 [elim] = fake_parts_extr_singleton [THEN [2] rev_subsetD]


lemma fake_parts_extr_insert: 
assumes "X \<in> fake bad IK CH"
shows "parts (extr bad IK' (insert X CH)) \<subseteq> parts (extr bad IK' CH) \<union> parts IK"
proof -
  have "parts (extr bad IK' (insert X CH)) \<subseteq> parts (extr bad IK' {X}) \<union> parts (extr bad IK' CH)" 
    by (auto simp: extr_insert_chan_eq [where CH=CH])
  also have "... \<subseteq> parts (extr bad IK' CH) \<union> parts IK" using assms
    by (auto dest!: fake_parts_extr_singleton)
  finally show ?thesis .
qed


lemma fake_synth_analz_extr: 
assumes  "X \<in> fake bad (synth (analz (extr bad IK CH))) CH"
shows "synth (analz (extr bad IK (insert X CH))) = synth (analz (extr bad IK CH))"
using assms
proof (intro equalityI) 
  have "synth (analz (extr bad IK (insert X CH))) 
     \<subseteq> synth (analz (extr bad IK {X} \<union> extr bad IK CH))"
    by - (rule synth_analz_mono, auto)
  also have "... \<subseteq> synth (analz (synth (analz (extr bad IK CH)) \<union> extr bad IK CH))" using assms
    by - (rule synth_analz_mono, auto)
  also have "... \<subseteq> synth (analz (synth (analz (extr bad IK CH))))"
    by - (rule synth_analz_mono, auto)
  also have "... \<subseteq> synth (analz (extr bad IK CH))" by simp
  finally show "synth (analz (extr bad IK (insert X CH))) \<subseteq> synth (analz (extr bad IK CH))" .
next
  have "extr bad IK CH \<subseteq> extr bad IK (insert X CH)"
    by auto
  then show "synth (analz (extr bad IK CH)) \<subseteq> synth (analz (extr bad IK (insert X CH)))"
    by - (rule synth_analz_mono, auto)
qed


(**************************************************************************************************)
subsection \<open>Closure of Dolev-Yao, extract and fake\<close>
(**************************************************************************************************)

subsubsection \<open>\<open>dy_fake_msg\<close>: returns messages, closure of DY and extr is sufficient\<close>
(**************************************************************************************************)

text \<open>Close @{term extr} under Dolev-Yao closure using @{term synth} and @{term analz}. 
This will be used in Level 2 attacker events to fake crypto messages.\<close>

definition 
  dy_fake_msg :: "agent set \<Rightarrow> msg set \<Rightarrow> chan set \<Rightarrow> msg set"
where
  "dy_fake_msg b i c = synth (analz (extr b i c))"


lemma dy_fake_msg_empty [simp]: "dy_fake_msg bad {} {} = synth {}"
by (auto simp add: dy_fake_msg_def)

lemma dy_fake_msg_mono_bad [dest]: "bad \<subseteq> bad' \<Longrightarrow> dy_fake_msg bad I C \<subseteq> dy_fake_msg bad' I C"
by (auto simp add: dy_fake_msg_def intro!: synth_analz_mono)

lemma dy_fake_msg_mono_ik [dest]: "G \<subseteq> H \<Longrightarrow> dy_fake_msg bad G C \<subseteq> dy_fake_msg bad H C"
by (auto simp add: dy_fake_msg_def intro!: synth_analz_mono)

lemma dy_fake_msg_mono_chan [dest]: "G \<subseteq> H \<Longrightarrow> dy_fake_msg bad I G \<subseteq> dy_fake_msg bad I H"
by (auto simp add: dy_fake_msg_def intro!: synth_analz_mono)
 
lemmas dy_fake_msg_monotone_bad [elim] = dy_fake_msg_mono_bad [THEN [2] rev_subsetD]
lemmas dy_fake_msg_monotone_ik [elim] = dy_fake_msg_mono_ik [THEN [2] rev_subsetD]
lemmas dy_fake_msg_monotone_chan [elim] = dy_fake_msg_mono_chan [THEN [2] rev_subsetD]

lemma dy_fake_msg_insert [intro]: 
  "M \<in> dy_fake_msg bad I C \<Longrightarrow> M \<in> dy_fake_msg bad I (insert X C)"
by (auto)

lemma dy_fake_msg_mono [intro]: 
  "\<lbrakk> b \<subseteq> b'; I \<subseteq> I'; C \<subseteq> C' \<rbrakk> \<Longrightarrow> dy_fake_msg b I C \<subseteq> dy_fake_msg b' I' C'"
by (force simp add: dy_fake_msg_def intro!: synth_analz_mono)

lemmas dy_fake_msg_monotone [elim] = dy_fake_msg_mono [THEN [2] rev_subsetD]

lemma dy_fake_msg_insert_chan:
  "x = insec \<or> x = auth \<Longrightarrow>
   M \<in> dy_fake_msg bad IK (insert (Chan x A B M) CH)"
by (auto simp add: dy_fake_msg_def)


subsubsection \<open>\<open>dy_fake_chan\<close>: returns channel messages\<close>
(**************************************************************************************************)

text \<open>The set of all channel messages that an attacker can fake is obtained using
@{term fake} with the sets of possible payload messages derived with @{term dy_fake_msg}
defined above. This will be used in Level 2 attacker events to fake channel messages.\<close>

definition
  dy_fake_chan :: "agent set \<Rightarrow> msg set \<Rightarrow> chan set \<Rightarrow> chan set"
where
  "dy_fake_chan b i c = fake b (dy_fake_msg b i c) c"


lemma dy_fake_chan_mono_bad [intro]: 
  "bad \<subseteq> bad' \<Longrightarrow> dy_fake_chan bad I C \<subseteq> dy_fake_chan bad' I C" 
by (auto simp add: dy_fake_chan_def)

lemma dy_fake_chan_mono_ik [intro]: 
  "T \<subseteq> T' \<Longrightarrow> dy_fake_chan bad T C \<subseteq> dy_fake_chan bad T' C" 
by (auto simp add: dy_fake_chan_def)

lemma dy_fake_chan_mono_chan [intro]: 
  "C \<subseteq> C' \<Longrightarrow> dy_fake_chan bad T C \<subseteq> dy_fake_chan bad T C'" 
by (auto simp add: dy_fake_chan_def)

lemmas dy_fake_chan_monotone_bad [elim] = dy_fake_chan_mono_bad [THEN [2] rev_subsetD]
lemmas dy_fake_chan_monotone_ik [elim] = dy_fake_chan_mono_ik [THEN [2] rev_subsetD]
lemmas dy_fake_chan_monotone_chan [elim] = dy_fake_chan_mono_chan [THEN [2] rev_subsetD]


lemma dy_fake_chan_mono [intro]: 
  assumes "b \<subseteq> b'" and "I \<subseteq> I'" and "C \<subseteq> C'"
  shows "dy_fake_chan b I C \<subseteq> dy_fake_chan b' I' C'"
proof -
  have "dy_fake_chan b I C \<subseteq> dy_fake_chan b' I C" using \<open>b \<subseteq> b'\<close> by auto
  also have "... \<subseteq> dy_fake_chan b' I' C" using \<open>I \<subseteq> I'\<close> by auto
  also have "... \<subseteq> dy_fake_chan b' I' C'" using \<open>C \<subseteq> C'\<close> by auto
  finally show ?thesis .
qed

lemmas dy_fake_chan_monotone [elim] = dy_fake_chan_mono [THEN [2] rev_subsetD]

lemma dy_fake_msg_subset_synth_analz: 
  "\<lbrakk>extr bad IK chan \<subseteq> T \<rbrakk> \<Longrightarrow> dy_fake_msg bad IK chan \<subseteq> synth (analz T)"
by (auto simp add: dy_fake_msg_def synth_analz_mono)

lemma dy_fake_chan_mono2:
  "\<lbrakk> extr bad IK chan \<subseteq> synth (analz y); chan \<subseteq> fake bad (synth (analz y)) z \<rbrakk>
 \<Longrightarrow> dy_fake_chan bad IK chan \<subseteq> fake bad (synth (analz y)) z"
apply (auto simp add: dy_fake_chan_def, erule fake.cases, auto)
apply (auto intro!: fake_New dest!: dy_fake_msg_subset_synth_analz)
done

lemma extr_subset_dy_fake_msg: "extr bad IK chan \<subseteq> dy_fake_msg bad IK chan"
by (auto simp add: dy_fake_msg_def)


lemma dy_fake_chan_extr_insert: 
  "M \<in> dy_fake_chan bad IK CH \<Longrightarrow> extr bad IK (insert M CH) \<subseteq> dy_fake_msg bad IK CH"
by (auto simp add: dy_fake_chan_def dy_fake_msg_def dest: fake_synth_analz_extr)

lemma dy_fake_chan_extr_insert_parts:
  "M \<in> dy_fake_chan bad IK CH \<Longrightarrow>
   parts (extr bad IK (insert M CH)) \<subseteq> parts (extr bad IK CH) \<union> dy_fake_msg bad IK CH"
by (drule dy_fake_chan_extr_insert [THEN parts_mono], auto simp add: dy_fake_msg_def)

lemma dy_fake_msg_extr: 
  "extr bad ik chan \<subseteq> synth (analz X) \<Longrightarrow> dy_fake_msg bad ik chan \<subseteq> synth (analz X)"
by (drule synth_analz_mono) (auto simp add: dy_fake_msg_def)

lemma extr_insert_dy_fake_msg:
  "M \<in> dy_fake_msg bad IK CH \<Longrightarrow> extr bad (insert M IK) CH \<subseteq> dy_fake_msg bad IK CH"
by (auto simp add: dy_fake_msg_def)

lemma dy_fake_msg_insert_dy_fake_msg:
  "M \<in> dy_fake_msg bad IK CH \<Longrightarrow> dy_fake_msg bad (insert M IK) CH \<subseteq> dy_fake_msg bad IK CH"
by (drule synth_analz_mono [OF extr_insert_dy_fake_msg], auto simp add: dy_fake_msg_def)

lemma synth_analz_insert_dy_fake_msg:
  "M \<in> dy_fake_msg bad IK CH \<Longrightarrow> synth (analz (insert M IK)) \<subseteq> dy_fake_msg bad IK CH"
by (auto dest!: dy_fake_msg_insert_dy_fake_msg, erule subsetD, 
    auto simp add: dy_fake_msg_def elim: synth_analz_monotone)

lemma Fake_insert_dy_fake_msg:
  "M \<in> dy_fake_msg bad IK CH \<Longrightarrow>
   extr bad IK CH \<subseteq> synth (analz X) \<Longrightarrow>
   synth (analz (insert M IK)) \<subseteq> synth (analz X)"
by (auto dest!: synth_analz_insert_dy_fake_msg dy_fake_msg_extr)

lemma dy_fake_chan_insert_chan:
  "x = insec \<or> x = auth \<Longrightarrow>
   Chan x A B M \<in> dy_fake_chan bad IK (insert (Chan x A B M) CH)"
by (auto simp add: dy_fake_chan_def)

lemma dy_fake_chan_subset:
  "CH \<subseteq> fake bad (dy_fake_msg bad IK CH) CH' \<Longrightarrow>
   dy_fake_chan bad IK CH \<subseteq> fake bad (dy_fake_msg bad IK CH) CH'"
by (auto simp add: dy_fake_chan_def)


end
