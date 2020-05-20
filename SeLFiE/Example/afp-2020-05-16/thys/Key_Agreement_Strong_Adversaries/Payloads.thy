(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Payloads.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Payloads.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Payload messages are messages that contain no implementation material,
  i.e. neither long-term keys nor channel tags; also:
  - auxiliary definitions: Keys_bad, broken, Enc_keys_clean 
  - lemmas for moving message sets out of 'analz'

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Payloads and Support for Channel Message Implementations\<close> 

text \<open>Definitions and lemmas that do not require the implementations.\<close>

theory Payloads
imports Message_derivation
begin

subsection \<open>Payload messages\<close>
(**************************************************************************************************)

text \<open>Payload messages contain no implementation material ie no long term keys or tags.\<close>

text \<open>Define set of payloads for basic messages.\<close>
inductive_set cpayload :: "cmsg set" where
  "cAgent A \<in> cpayload"
| "cNumber T \<in> cpayload"
| "cNonce N \<in> cpayload"
| "cEphK K \<in> cpayload"
| "X \<in> cpayload \<Longrightarrow> cHash X \<in> cpayload"
| "\<lbrakk> X \<in> cpayload; Y \<in> cpayload \<rbrakk> \<Longrightarrow> cPair X Y \<in> cpayload"
| "\<lbrakk> X \<in> cpayload; Y \<in> cpayload \<rbrakk> \<Longrightarrow> cEnc X Y \<in> cpayload"
| "\<lbrakk> X \<in> cpayload; Y \<in> cpayload \<rbrakk> \<Longrightarrow> cAenc X Y \<in> cpayload"
| "\<lbrakk> X \<in> cpayload; Y \<in> cpayload \<rbrakk> \<Longrightarrow> cSign X Y \<in> cpayload"
| "\<lbrakk> X \<in> cpayload; Y \<in> cpayload \<rbrakk> \<Longrightarrow> cExp X Y \<in> cpayload"

text \<open>Lift @{term cpayload} to the quotiented message type.\<close>
lift_definition payload :: "msg set" is cpayload by -

text \<open>Lemmas used to prove the intro and inversion rules for @{term payload}.\<close>
lemma eq_rep_abs: "eq x (Re (Ab x))"
by (simp add: Quotient3_msg rep_abs_rsp)


lemma eq_cpayload:
  assumes "eq x y" and "x \<in> cpayload"
  shows "y \<in> cpayload"
using assms by (induction x y rule: eq.induct, auto intro: cpayload.intros elim: cpayload.cases)

lemma abs_payload: "Ab x \<in> payload \<longleftrightarrow> x \<in> cpayload"
by (auto simp add: payload_def msg.abs_eq_iff eq_cpayload eq_sym cpayload.intros 
         elim: cpayload.cases)

lemma abs_cpayload_rep: "x \<in> Ab` cpayload \<longleftrightarrow> Re x \<in> cpayload"
apply (auto elim: eq_cpayload [OF eq_rep_abs])
apply (subgoal_tac "x = Ab (Re x)", auto)
using Quotient3_abs_rep Quotient3_msg by fastforce

lemma payload_rep_cpayload: "Re x \<in> cpayload \<longleftrightarrow> x \<in> payload"
by (auto simp add: payload_def abs_cpayload_rep)

text \<open>Manual proof of payload introduction rules. Transfer does not work for these\<close>

declare cpayload.intros [intro]
lemma payload_AgentI: "Agent A \<in> payload"
  by (auto simp add: msg_defs abs_payload)
lemma payload_NonceI: "Nonce N \<in> payload"
  by (auto simp add: msg_defs abs_payload)
lemma payload_NumberI: "Number N \<in> payload"
  by (auto simp add: msg_defs abs_payload)
lemma payload_EphKI: "EphK X \<in> payload"
  by (auto simp add: msg_defs abs_payload)
lemma payload_HashI: "x \<in> payload \<Longrightarrow> Hash x \<in> payload"
  by (auto simp add: msg_defs payload_rep_cpayload abs_payload)
lemma payload_PairI: "x \<in> payload \<Longrightarrow> y \<in> payload \<Longrightarrow> Pair x y \<in> payload"
  by (auto simp add: msg_defs payload_rep_cpayload abs_payload)
lemma payload_EncI: "x \<in> payload \<Longrightarrow> y \<in> payload \<Longrightarrow> Enc x y \<in> payload"
  by (auto simp add: msg_defs payload_rep_cpayload abs_payload)
lemma payload_AencI: "x \<in> payload \<Longrightarrow> y \<in> payload \<Longrightarrow> Aenc x y \<in> payload"
  by (auto simp add: msg_defs payload_rep_cpayload abs_payload)
lemma payload_SignI: "x \<in> payload \<Longrightarrow> y \<in> payload \<Longrightarrow> Sign x y \<in> payload"
  by (auto simp add: msg_defs payload_rep_cpayload abs_payload)
lemma payload_ExpI: "x \<in> payload \<Longrightarrow> y \<in> payload \<Longrightarrow> Exp x y \<in> payload"
by (auto simp add: msg_defs payload_rep_cpayload abs_payload)

lemmas payload_intros [simp, intro] =
  payload_AgentI payload_NonceI payload_NumberI payload_EphKI payload_HashI
  payload_PairI payload_EncI payload_AencI payload_SignI payload_ExpI

text \<open>Manual proof of payload inversion rules, transfer does not work for these.\<close>

declare cpayload.cases[elim]
lemma payload_Tag: "Tag X \<in> payload \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done

lemma payload_LtK: "LtK X \<in> payload \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Hash: "Hash X \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Pair: "Pair X Y \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Enc: "Enc X Y \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Aenc: "Aenc X Y \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Sign: "Sign X Y \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def msg_defs msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done
lemma payload_Exp: "Exp X Y \<in> payload \<Longrightarrow> (X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow> P"
apply (auto simp add: payload_def Exp_def msg.abs_eq_iff eq_sym)
apply (auto dest!: eq_cpayload simp add: abs_cpayload_rep)
done

declare cpayload.intros[rule del]
declare cpayload.cases[rule del]

lemmas payload_inductive_cases =
  payload_Tag payload_LtK payload_Hash
  payload_Pair payload_Enc payload_Aenc payload_Sign payload_Exp

lemma eq_exhaust:
"(\<And>x. eq y (cAgent x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cNumber x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cNonce x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cLtK x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cEphK x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. eq y (cPair x x') \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. eq y (cEnc x x') \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. eq y (cAenc x x') \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. eq y (cSign x x') \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cHash x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. eq y (cTag x) \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. eq y (cExp x x') \<Longrightarrow> P) \<Longrightarrow>
 P"
apply (cases y)
apply (meson Messages.eq_refl)+
done

lemma msg_exhaust:
"(\<And>x. y = Agent x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = Number x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = Nonce x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = LtK x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = EphK x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. y = Pair x x' \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. y = Enc x x' \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. y = Aenc x x' \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. y = Sign x x' \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = Hash x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x. y = Tag x \<Longrightarrow> P) \<Longrightarrow>
 (\<And>x x'. y = Exp x x' \<Longrightarrow> P) \<Longrightarrow>
 P"
apply transfer
apply (erule eq_exhaust, auto)
done

lemma payload_cases: 
"a \<in> payload \<Longrightarrow>
(\<And>A. a = Agent A \<Longrightarrow> P) \<Longrightarrow>
(\<And>T. a = Number T \<Longrightarrow> P) \<Longrightarrow>
(\<And>N. a = Nonce N \<Longrightarrow> P) \<Longrightarrow>
(\<And>K. a = EphK K \<Longrightarrow> P) \<Longrightarrow>
(\<And>X. a = Hash X \<Longrightarrow> X \<in> payload \<Longrightarrow> P) \<Longrightarrow>
(\<And>X Y. a = Pair X Y \<Longrightarrow> X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow>
(\<And>X Y. a = Enc X Y \<Longrightarrow> X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow>
(\<And>X Y. a = Aenc X Y \<Longrightarrow> X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow>
(\<And>X Y. a = Sign X Y \<Longrightarrow> X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow>
(\<And>X Y. a = Exp X Y \<Longrightarrow> X \<in> payload \<Longrightarrow> Y \<in> payload \<Longrightarrow> P) \<Longrightarrow>
 P"
by (erule msg_exhaust [of a], auto elim: payload_inductive_cases)

declare payload_cases [elim]
declare payload_inductive_cases [elim]

text \<open>Properties of payload; messages constructed from payload messages are also payloads.\<close>

lemma payload_parts [simp, dest]:
  "\<lbrakk> X \<in> parts S; S \<subseteq> payload \<rbrakk> \<Longrightarrow> X \<in> payload" 
by (erule parts.induct) (auto)

lemma payload_parts_singleton [simp, dest]:
  "\<lbrakk> X \<in> parts {Y}; Y \<in> payload \<rbrakk> \<Longrightarrow> X \<in> payload" 
by (erule parts.induct) (auto)

lemma payload_analz [simp, dest]:
  "\<lbrakk> X \<in> analz S; S \<subseteq> payload \<rbrakk> \<Longrightarrow> X \<in> payload" 
by (auto dest: analz_into_parts)

lemma payload_synth_analz: 
  "\<lbrakk> X \<in> synth (analz S); S \<subseteq> payload \<rbrakk> \<Longrightarrow> X \<in> payload" 
by (erule synth.induct) (auto intro: payload_analz)

text \<open>Important lemma: using messages with implementation material one can only 
synthesise more such messages.\<close>

lemma synth_payload: 
  "Y \<inter> payload = {} \<Longrightarrow> synth (X \<union> Y) \<subseteq> synth X \<union> -payload"
by (rule, erule synth.induct) (auto) 

lemma synth_payload2:
  "Y \<inter> payload = {} \<Longrightarrow> synth (Y \<union> X) \<subseteq> synth X \<union> -payload"
by (rule, erule synth.induct) (auto) 

text \<open>Lemma: in the case of the previous lemma, @{term synth} can be applied on the 
left with no consequence.\<close>

lemma synth_idem_payload:
  "X \<subseteq> synth Y \<union> -payload \<Longrightarrow> synth X \<subseteq> synth Y \<union> -payload"
by (auto dest: synth_mono subset_trans [OF _ synth_payload])


subsection \<open>\<open>isLtKey\<close>: is a long term key\<close>
(**************************************************************************************************)

lemma LtKeys_payload [dest]: "NI \<subseteq> payload \<Longrightarrow> NI \<inter> range LtK = {}"
by (auto)

lemma LtKeys_parts_payload [dest]: "NI \<subseteq> payload \<Longrightarrow> parts NI \<inter> range LtK = {}"
by (auto)

lemma LtKeys_parts_payload_singleton [elim]: "X \<in> payload \<Longrightarrow> LtK Y \<in> parts {X} \<Longrightarrow> False"
by (auto)

lemma parts_of_LtKeys [simp]: "K \<subseteq> range LtK \<Longrightarrow> parts K = K"
by (rule, rule, erule parts.induct, auto) 


subsection\<open>\<open>keys_of\<close>: the long term keys of an agent\<close>
(**************************************************************************************************)

definition
  keys_of :: "agent \<Rightarrow> msg set"
where
  "keys_of A \<equiv> insert (priK A) {shrK B C | B C. B = A \<or> C = A}"

lemma keys_of_Ltk [intro!]: "keys_of A \<subseteq> range LtK"
by (auto simp add: keys_of_def)

lemma priK_keys_of [intro!]:
  "priK A \<in> keys_of A"
by (simp add: keys_of_def)

lemma shrK_keys_of_1 [intro!]:
  "shrK A B \<in> keys_of A"
by (simp add: keys_of_def)

lemma shrK_keys_of_2 [intro!]:
  "shrK B A \<in> keys_of A"
by (simp add: keys_of_def)
lemma priK_keys_of_eq [dest]:
  "priK B \<in> keys_of A \<Longrightarrow> A = B"
by (simp add: keys_of_def)

lemma shrK_keys_of_eq [dest]:
  "shrK A B \<in> keys_of C \<Longrightarrow> A = C \<or> B = C"
by (simp add: keys_of_def)

lemma def_keys_of [dest]:
  "K \<in> keys_of A \<Longrightarrow> K = priK A \<or> (\<exists> B. K = shrK A B \<or> K = shrK B A)"
by (auto simp add: keys_of_def)

lemma parts_keys_of [simp]: "parts (keys_of A) = keys_of A"
by (auto intro!: parts_of_LtKeys)


lemma analz_keys_of [simp]: "analz (keys_of A) = keys_of A"
by (rule, rule, erule analz.induct, auto)

subsection \<open>\<open>Keys_bad\<close>: bounds on the attacker's knowledge of long-term keys.\<close>
(**************************************************************************************************)

text \<open>A set of keys contains all public long term keys, and only the private/shared keys 
of bad agents.\<close>

definition
  Keys_bad :: "msg set \<Rightarrow> agent set \<Rightarrow> bool"
where
  "Keys_bad IK Bad \<equiv>    
    IK \<inter> range LtK \<subseteq> range pubK \<union> \<Union> (keys_of ` Bad)
    \<and> range pubK \<subseteq> IK"

\<comment> \<open>basic lemmas\<close>

lemma Keys_badI:
  "\<lbrakk> IK \<inter> range LtK \<subseteq> range pubK \<union> priK`Bad \<union> {shrK A B | A B. A \<in> Bad \<or> B \<in> Bad}; 
     range pubK \<subseteq> IK  \<rbrakk>
 \<Longrightarrow> Keys_bad IK Bad"
by (auto simp add: Keys_bad_def)

lemma Keys_badE [elim]: 
  "\<lbrakk> Keys_bad IK Bad;
     \<lbrakk> range pubK \<subseteq> IK; 
       IK \<inter> range LtK \<subseteq> range pubK \<union> \<Union> (keys_of ` Bad)\<rbrakk>
   \<Longrightarrow> P \<rbrakk> 
 \<Longrightarrow> P"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_Ltk [simp]:
  "Keys_bad (IK \<inter> range LtK) Bad \<longleftrightarrow> Keys_bad IK Bad"
by (auto simp add: Keys_bad_def)


lemma Keys_bad_priK_D: "\<lbrakk> priK A \<in> IK; Keys_bad IK Bad \<rbrakk> \<Longrightarrow> A \<in> Bad"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_shrK_D: "\<lbrakk> shrK A B \<in> IK; Keys_bad IK Bad \<rbrakk> \<Longrightarrow> A \<in> Bad \<or> B \<in> Bad"
by (auto simp add: Keys_bad_def)

lemmas Keys_bad_dests [dest] = Keys_bad_priK_D Keys_bad_shrK_D


text \<open>interaction with @{term insert}.\<close>

lemma Keys_bad_insert_non_LtK: 
  "X \<notin> range LtK \<Longrightarrow> Keys_bad (insert X IK) Bad \<longleftrightarrow> Keys_bad IK Bad"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_insert_pubK: 
  "\<lbrakk> Keys_bad IK Bad \<rbrakk> \<Longrightarrow> Keys_bad (insert (pubK A) IK) Bad"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_insert_priK_bad: 
  "\<lbrakk> Keys_bad IK Bad; A \<in> Bad \<rbrakk> \<Longrightarrow> Keys_bad (insert (priK A) IK) Bad"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_insert_shrK_bad: 
  "\<lbrakk> Keys_bad IK Bad; A \<in> Bad \<or> B \<in> Bad \<rbrakk> \<Longrightarrow> Keys_bad (insert (shrK A B) IK) Bad"
by (auto simp add: Keys_bad_def)

lemmas Keys_bad_insert_lemmas [simp] = 
  Keys_bad_insert_non_LtK Keys_bad_insert_pubK 
  Keys_bad_insert_priK_bad Keys_bad_insert_shrK_bad


lemma Keys_bad_insert_Fake:
assumes "Keys_bad IK Bad" 
    and "parts IK \<inter> range LtK \<subseteq> IK"
    and "X \<in> synth (analz IK)"
shows "Keys_bad (insert X IK) Bad"
proof cases
  assume "X \<in> range LtK"
  then obtain ltk where "X = LtK ltk" by blast
  thus ?thesis using assms
    by (auto simp add: insert_absorb dest: analz_into_parts)
next 
  assume "X \<notin> range LtK"
  thus ?thesis using assms(1) by simp
qed


lemma Keys_bad_insert_keys_of:
  "Keys_bad Ik Bad \<Longrightarrow>
   Keys_bad (keys_of A \<union> Ik) (insert A Bad)"
by (auto simp add: Keys_bad_def)

lemma Keys_bad_insert_payload:
  "Keys_bad Ik Bad \<Longrightarrow>
   x \<in> payload \<Longrightarrow>
   Keys_bad (insert x Ik) Bad"
by (auto simp add: Keys_bad_def)


subsection \<open>\<open>broken K\<close>: pairs of agents where at least one is compromised.\<close>
(**************************************************************************************************)

text \<open>Set of pairs (A,B) such that the priK of A or B, or their shared key, is in K\<close>

definition
  broken :: "msg set \<Rightarrow> (agent * agent) set"
where
  "broken K \<equiv> {(A,B) | A B. priK A \<in> K \<or> priK B \<in> K \<or> shrK A B \<in> K \<or> shrK B A \<in> K}"

lemma brokenD [dest!]:
  "(A, B) \<in> broken K \<Longrightarrow> priK A \<in> K \<or> priK B \<in> K \<or> shrK A B \<in> K \<or> shrK B A \<in> K"
by (simp add: broken_def)

lemma brokenI [intro!]:
  "priK A \<in> K \<or> priK B \<in> K \<or> shrK A B \<in> K \<or> shrK B A \<in> K \<Longrightarrow> (A, B) \<in> broken K"
by (auto simp add: broken_def)


subsection \<open>\<open>Enc_keys_clean S\<close>: messages with ``clean'' symmetric encryptions.\<close>
(**************************************************************************************************)

text \<open>All terms used as symmetric keys in S are either long term keys or messages without 
implementation material.\<close>

definition
  Enc_keys_clean :: "msg set \<Rightarrow> bool"
where
  "Enc_keys_clean S \<equiv> \<forall>X Y. Enc X Y \<in> parts S \<longrightarrow> Y \<in> range LtK \<union> payload"

lemma Enc_keys_cleanI:
  "\<forall>X Y. Enc X Y \<in> parts S \<longrightarrow> Y \<in> range LtK \<union> payload \<Longrightarrow> Enc_keys_clean S"
by (simp add: Enc_keys_clean_def)

\<comment> \<open>general lemmas about \<open>Enc_keys_clean\<close>\<close>
lemma Enc_keys_clean_mono: 
  "Enc_keys_clean H \<Longrightarrow> G \<subseteq> H \<Longrightarrow> Enc_keys_clean G"  \<comment> \<open>anti-tone\<close>
by (auto simp add: Enc_keys_clean_def dest!: parts_monotone [where G=G])

lemma Enc_keys_clean_Un [simp]: 
  "Enc_keys_clean (G \<union> H) \<longleftrightarrow> Enc_keys_clean G \<and> Enc_keys_clean H" 
by (auto simp add: Enc_keys_clean_def)


\<comment> \<open>from \<open>Enc_keys_clean S\<close>, the property on \<open>parts S\<close> also holds for \<open>analz S\<close>\<close>
lemma Enc_keys_clean_analz:
  "Enc X K \<in> analz S \<Longrightarrow> Enc_keys_clean S \<Longrightarrow> K \<in> range LtK \<union> payload"
by (auto simp add: Enc_keys_clean_def dest: analz_into_parts)


\<comment> \<open>\<open>Enc_keys_clean\<close> and different types of messages\<close>
lemma Enc_keys_clean_Tags [simp,intro]: "Enc_keys_clean Tags"
by (auto simp add: Enc_keys_clean_def)

lemma Enc_keys_clean_LtKeys [simp,intro]: "K \<subseteq> range LtK \<Longrightarrow> Enc_keys_clean K"
by (auto simp add: Enc_keys_clean_def)

lemma Enc_keys_clean_payload [simp,intro]: "NI \<subseteq> payload \<Longrightarrow> Enc_keys_clean NI"
by (auto simp add: Enc_keys_clean_def)


subsection \<open>Sets of messages with particular constructors\<close>
(**************************************************************************************************)

text \<open>Sets of all pairs, ciphertexts, and signatures constructed from a set of messages.\<close>
(*
 FIX: These should probably be turned into definitions, since they may create automation problems 
*)
abbreviation AgentSet :: "msg set"
where "AgentSet \<equiv> range Agent"

abbreviation PairSet :: "msg set \<Rightarrow> msg set \<Rightarrow> msg set"
where "PairSet G H \<equiv> {Pair X Y | X Y. X \<in> G \<and> Y \<in> H}"

abbreviation EncSet :: "msg set \<Rightarrow> msg set \<Rightarrow> msg set"
where "EncSet G K \<equiv> {Enc X Y | X Y. X \<in> G \<and> Y \<in> K}"

abbreviation AencSet :: "msg set \<Rightarrow> msg set \<Rightarrow> msg set"
where "AencSet G K \<equiv> {Aenc X Y | X Y. X \<in> G \<and> Y \<in> K}"

abbreviation SignSet :: "msg set \<Rightarrow> msg set \<Rightarrow> msg set"
where "SignSet G K \<equiv> {Sign X Y | X Y. X \<in> G \<and> Y \<in> K}"

abbreviation HashSet :: "msg set \<Rightarrow> msg set"
where "HashSet G \<equiv> {Hash X | X. X \<in> G}"


text \<open>Move @{term Enc}, @{term Aenc}, @{term Sign}, and @{term Pair} sets out of @{term parts}. 
\<close>

lemma parts_PairSet:
  "parts (PairSet G H) \<subseteq> PairSet G H \<union> parts G \<union> parts H"
by (rule, erule parts.induct, auto)

lemma parts_EncSet:
  "parts (EncSet G K) \<subseteq> EncSet G K \<union> PairSet (range Agent) G  \<union> range Agent \<union>  parts G"
by (rule, erule parts.induct, auto)

lemma parts_AencSet:
  "parts (AencSet G K) \<subseteq> AencSet G K \<union> PairSet (range Agent) G  \<union> range Agent \<union>  parts G"
by (rule, erule parts.induct, auto)

lemma parts_SignSet:
  "parts (SignSet G K) \<subseteq> SignSet G K \<union> PairSet (range Agent) G  \<union> range Agent \<union>  parts G"
by (rule, erule parts.induct, auto)

lemma parts_HashSet:
  "parts (HashSet G) \<subseteq> HashSet G"
by (rule, erule parts.induct, auto)

lemmas parts_msgSet = parts_PairSet parts_EncSet parts_AencSet parts_SignSet parts_HashSet
lemmas parts_msgSetD = parts_msgSet [THEN [2] rev_subsetD]

text \<open>
Remove the message sets from under the @{term "Enc_keys_clean"} predicate.
Only when the first part is a set of agents or tags for @{term Pair}, this is sufficient.\<close>

lemma Enc_keys_clean_PairSet_Agent_Un: 
  "Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (PairSet (Agent`X) G \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemma Enc_keys_clean_PairSet_Tag_Un: 
  "Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (PairSet Tags G \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemma Enc_keys_clean_AencSet_Un: 
  "Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (AencSet G K \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemma Enc_keys_clean_EncSet_Un: 
  "K \<subseteq> range LtK \<Longrightarrow> Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (EncSet G K \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemma Enc_keys_clean_SignSet_Un: 
  "Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (SignSet G K \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemma Enc_keys_clean_HashSet_Un: 
  "Enc_keys_clean (G \<union> H) \<Longrightarrow> Enc_keys_clean (HashSet G \<union> H)"
by (auto simp add: Enc_keys_clean_def dest!: parts_msgSetD)

lemmas Enc_keys_clean_msgSet_Un =
  Enc_keys_clean_PairSet_Tag_Un Enc_keys_clean_PairSet_Agent_Un
  Enc_keys_clean_EncSet_Un Enc_keys_clean_AencSet_Un
  Enc_keys_clean_SignSet_Un Enc_keys_clean_HashSet_Un


subsubsection \<open>Lemmas for moving message sets out of @{term "analz"}\<close>
(**************************************************************************************************)

text \<open>Pull @{term EncSet} out of @{term analz}.\<close>

lemma analz_Un_EncSet:
assumes "K \<subseteq> range LtK" and "Enc_keys_clean (G \<union> H)" 
shows "analz (EncSet G K \<union> H) \<subseteq> EncSet G K \<union> analz (G \<union> H)"
proof 
  fix X
  assume "X \<in> analz (EncSet G K \<union> H)"
  thus "X \<in> EncSet G K \<union> analz (G \<union> H)"
  proof (induction X rule: analz.induct)
    case (Dec Y K')     
    from Dec.IH(1) show ?case
    proof
      assume "Enc Y K' \<in> analz (G \<union> H)"
      have "K' \<in> synth (analz (G \<union> H))"
      proof -
        have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz (G \<union> H)\<close> assms(2)
          by (blast dest: Enc_keys_clean_analz)
        moreover
        have "K' \<in> synth (EncSet G K \<union> analz (G \<union> H))" using Dec.IH(2)
          by (auto simp add: Collect_disj_eq dest: synth_Int2)
        moreover
        hence "K' \<in> synth (analz (G \<union> H)) \<union> -payload" using assms(1) 
          by (blast dest!: synth_payload2 [THEN [2] rev_subsetD])
        ultimately show ?thesis by auto
      qed  
      thus ?case using \<open>Enc Y K' \<in> analz (G \<union> H)\<close> by auto
    qed auto
  next
    case (Adec_eph Y K')  
    thus ?case by (auto dest!: EpriK_synth)
  qed (auto)
qed 

text \<open>Pull @{term EncSet} out of @{term analz}, 2nd case: the keys are unknown.\<close>

lemma analz_Un_EncSet2:
assumes "Enc_keys_clean H" and "K \<subseteq> range LtK" and "K \<inter> synth (analz H) = {}"
shows "analz (EncSet G K \<union> H) \<subseteq> EncSet G K \<union> analz H"
proof 
  fix X
  assume "X \<in> analz (EncSet G K \<union> H)"
  thus "X \<in> EncSet G K \<union> analz H"
  proof (induction X rule: analz.induct)
    case (Dec Y K')
    from Dec.IH(1) show ?case 
    proof
      assume "Enc Y K' \<in> analz H"
      moreover have "K' \<in> synth (analz H)"
      proof -
          have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz H\<close> assms(1)
            by (auto dest: Enc_keys_clean_analz)
          moreover
          from Dec.IH(2) have H: "K' \<in> synth (EncSet G K \<union> analz H)" 
            by (auto simp add: Collect_disj_eq dest: synth_Int2)
          moreover
          hence "K' \<in> synth (analz H) \<union> -payload" 
          proof (rule synth_payload2 [THEN [2] rev_subsetD], auto elim!: payload_Enc)
            fix X Y
            assume "Y \<in> K" "Y \<in> payload"
            with \<open>K \<subseteq> range LtK\<close> obtain KK where "Y = LtK KK" by auto
            with \<open>Y \<in> payload\<close> show False by auto
          qed
        ultimately 
        show ?thesis by auto
      qed
      ultimately show ?case by auto
    next
      assume "Enc Y K' \<in> EncSet G K"
      moreover hence "K' \<in> K" by auto
      moreover with \<open>K \<subseteq> range LtK\<close> obtain KK where "K' = LtK KK" by auto
      moreover with Dec.IH(2) have "K' \<in> analz H" 
        by (auto simp add: Collect_disj_eq dest: synth_Int2)
      ultimately show ?case using \<open>K \<inter> synth (analz H) = {}\<close> by auto
    qed
  next 
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed (insert assms(2), auto)
qed


text \<open>Pull @{term AencSet} out of the @{term analz}.\<close>

lemma analz_Un_AencSet:
assumes "K \<subseteq> range LtK" and "Enc_keys_clean (G \<union> H)" 
shows "analz (AencSet G K \<union> H) \<subseteq> AencSet G K \<union> analz (G \<union> H)"
proof 
  fix X
  assume "X \<in> analz (AencSet G K \<union> H)"
  thus "X \<in> AencSet G K \<union> analz (G \<union> H)"
  proof (induction X rule: analz.induct)
    case (Dec Y K') 
    from Dec.IH(1) have "Enc Y K' \<in> analz (G \<union> H)" by auto
    moreover have "K' \<in> synth (analz (G \<union> H))" 
    proof -
      have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz (G \<union> H)\<close> assms(2) 
        by (blast dest: Enc_keys_clean_analz)
      moreover
      have "K' \<in> synth (AencSet G K \<union> analz (G \<union> H))" using Dec.IH(2)
        by (auto simp add: Collect_disj_eq dest: synth_Int2)
      moreover
      hence "K' \<in> synth (analz (G \<union> H)) \<union> -payload" using assms(1) 
        by (blast dest!: synth_payload2 [THEN [2] rev_subsetD])
      ultimately 
      show ?thesis by auto 
    qed
    ultimately show ?case by auto
  next 
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed auto
qed

text \<open>Pull @{term AencSet} out of @{term analz}, 2nd case: the keys are unknown.\<close>

lemma analz_Un_AencSet2:
assumes "Enc_keys_clean H" and "priK`Ag \<inter> synth (analz H) = {}"
shows "analz (AencSet G (pubK`Ag) \<union> H) \<subseteq> AencSet G (pubK`Ag) \<union> analz H"
proof 
  fix X
  assume "X \<in> analz (AencSet G (pubK` Ag) \<union> H)"
  thus "X \<in> AencSet G (pubK` Ag) \<union> analz H"
  proof (induction X rule: analz.induct)
    case (Dec Y K') 
    from Dec.IH(1) have "Enc Y K' \<in> analz H" by auto
    moreover have "K' \<in> synth (analz H)"
    proof -
      have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz H\<close> assms(1)
      by (auto dest: Enc_keys_clean_analz)
      moreover
      from Dec.IH(2) have H: "K' \<in> synth (AencSet G (pubK`Ag) \<union> analz H)" 
        by (auto simp add: Collect_disj_eq dest: synth_Int2)
      moreover
      hence "K' \<in> synth (analz H) \<union> -payload" 
        by (auto dest: synth_payload2 [THEN [2] rev_subsetD])
      ultimately 
      show ?thesis by auto
    qed
    ultimately show ?case by auto
  next 
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed (insert assms(2), auto)
qed

text \<open>Pull @{term PairSet} out of @{term analz}.\<close>
lemma analz_Un_PairSet:
  "analz (PairSet G G' \<union> H) \<subseteq> PairSet G G' \<union> analz (G \<union> G' \<union> H)"
proof 
  fix X
  assume "X \<in> analz (PairSet G G' \<union> H)"
  thus "X \<in> PairSet G G' \<union> analz (G \<union> G' \<union> H)"
  proof (induct X rule: analz.induct)
    case (Dec Y K) 
    from Dec.hyps(2) have "Enc Y K \<in> analz (G \<union> G' \<union> H)" by auto
    moreover
    from Dec.hyps(3) have "K \<in> synth (PairSet G G' \<union> analz (G \<union> G' \<union> H))"
      by (auto simp add: Collect_disj_eq dest: synth_Int2)
    then have "K \<in> synth (analz (G \<union> G' \<union> H))"
      by (elim synth_trans) auto
    ultimately
    show ?case by auto
  next 
    case (Adec_eph Y K) 
    thus ?case by (auto dest!: EpriK_synth)
  qed auto
qed

\<comment> \<open>move the \<open>SignSet\<close> out of the \<open>analz\<close>\<close>
lemma analz_Un_SignSet:
assumes "K \<subseteq> range LtK" and "Enc_keys_clean (G \<union> H)"
shows "analz (SignSet G K \<union> H) \<subseteq> SignSet G K \<union> analz (G \<union> H)"
proof 
  fix X
  assume "X \<in> analz (SignSet G K \<union> H)"
  thus "X \<in> SignSet G K \<union> analz (G \<union> H)"
  proof (induct X rule: analz.induct)
    case (Dec Y K') 
    from Dec.hyps(2) have "Enc Y K' \<in> analz (G \<union> H)" by auto
    moreover have "K' \<in> synth (analz (G \<union> H))"
    proof -
      have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz (G \<union> H)\<close> assms(2) 
        by (blast dest: Enc_keys_clean_analz)
      moreover
      from Dec.hyps(3) have "K' \<in> synth (SignSet G K \<union> analz (G \<union> H)) "
        by (auto simp add: Collect_disj_eq dest: synth_Int2)
      moreover
      hence "K' \<in> synth (analz (G \<union> H)) \<union> -payload" using assms(1) 
        by (blast dest!: synth_payload2 [THEN [2] rev_subsetD])
      ultimately 
      show ?thesis by auto
    qed
    ultimately show ?case by auto
  next 
    case (Adec_eph Y K) 
    thus ?case by (auto dest!: EpriK_synth)
  qed auto
qed

text \<open>Pull @{term Tags} out of @{term analz}.\<close>

lemma analz_Un_Tag:
assumes "Enc_keys_clean H"
shows "analz (Tags \<union> H) \<subseteq> Tags \<union> analz H"
proof 
  fix X
  assume "X \<in> analz (Tags \<union> H)"
  thus "X \<in> Tags \<union> analz H"
  proof (induction X rule: analz.induct)
    case (Dec Y K') 
    have "Enc Y K' \<in> analz H" using Dec.IH(1) by auto
    moreover have "K' \<in> synth (analz H)" 
    proof -
      have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz H\<close> assms 
        by (auto dest: Enc_keys_clean_analz)
      moreover
      from Dec.IH(2) have "K' \<in> synth (Tags \<union> analz H)" 
        by (auto simp add: Collect_disj_eq dest: synth_Int2)
      moreover
      hence "K' \<in> synth (analz H) \<union> -payload" 
        by (auto dest: synth_payload2 [THEN [2] rev_subsetD]) 
      ultimately show ?thesis by auto
    qed
    ultimately show ?case by (auto)
  next
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed auto
qed 

text \<open>Pull the @{term AgentSet} out of the @{term analz}.\<close>

lemma analz_Un_AgentSet:
shows "analz (AgentSet \<union> H) \<subseteq> AgentSet \<union> analz H"
proof 
  fix X
  assume "X \<in> analz (AgentSet \<union> H)"
  thus "X \<in> AgentSet \<union> analz H"
  proof (induction X rule: analz.induct)
    case (Dec Y K') 
    from Dec.IH(1) have "Enc Y K' \<in> analz H" by auto
    moreover have "K' \<in> synth (analz H)" 
      proof -
        from Dec.IH(2) have "K' \<in> synth (AgentSet \<union> analz H)" 
          by (auto simp add: Collect_disj_eq dest: synth_Int2)
        moreover have "synth (AgentSet \<union> analz H) \<subseteq> synth (analz H)" 
          by (auto simp add: synth_subset_iff)
        ultimately show ?thesis by auto
    qed
    ultimately show ?case by (auto)
  next
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed auto
qed 

text \<open>Pull @{term HashSet} out of @{term analz}.\<close>
lemma analz_Un_HashSet:
assumes "Enc_keys_clean H" and "G \<subseteq> - payload" 
shows "analz (HashSet G  \<union> H) \<subseteq> HashSet G \<union> analz H"
proof 
  fix X
  assume "X \<in> analz (HashSet G \<union> H)"
  thus "X \<in> HashSet G \<union> analz H"
  proof (induction X rule: analz.induct)
    case (Dec Y K')
    from Dec.IH(1) have "Enc Y K' \<in> analz H" by auto
    moreover have "K' \<in> synth (analz H)"
    proof -
      have "K' \<in> range LtK \<union> payload" using \<open>Enc Y K' \<in> analz H\<close> assms(1)
      by (auto dest: Enc_keys_clean_analz)
      thus ?thesis
      proof
        assume "K' \<in> range LtK"
        then obtain KK where "K' = LtK KK" by auto
        moreover
        with Dec.IH(2) show ?thesis
          by (auto simp add: Collect_disj_eq dest: synth_Int2)
      next
        assume "K' \<in> payload"  
        moreover
        from assms have "HashSet G \<inter> payload = {}" by auto
        moreover from Dec.IH(2) have "K' \<in> synth (HashSet G \<union> analz H)" 
          by (auto simp add: Collect_disj_eq dest: synth_Int2)
        ultimately
        have "K' \<in> synth (analz H) \<union> -payload" 
          by (auto dest: synth_payload2 [THEN [2] rev_subsetD])
        with \<open>K' \<in> payload\<close> show ?thesis by auto 
      qed
    qed
    ultimately show ?case by auto
  next 
    case (Adec_eph Y K') 
    thus ?case by (auto dest!: EpriK_synth)
  qed (insert assms(2), auto)
qed

end
